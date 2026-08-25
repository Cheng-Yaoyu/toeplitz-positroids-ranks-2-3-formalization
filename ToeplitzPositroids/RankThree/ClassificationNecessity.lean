import ToeplitzPositroids.RankThree.CollinearIntervals
import ToeplitzPositroids.RankThree.CompatibleData
import ToeplitzPositroids.RankThree.EndpointParallel
import ToeplitzPositroids.RankThree.SupportUniqueness
import Lean.Elab.Tactic.Omega

/-!
# Necessity in the rank-three Toeplitz classification

This file packages the geometric and Toeplitz-structural results into the
canonical compatible data of the classification.  The construction is derived
from the matrix itself: loops, positive-parallel classes, and maximal collinear
intervals are not supplied as external data.
-/

namespace ToeplitzPositroids

open Matrix
open RankThree

noncomputable section

variable {n : ℕ} {a : Fin (n + 2) → ℝ}

/-- Full row rank of a three-row matrix forces at least three columns. -/
theorem three_le_of_hasFullRowRank {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A) : 3 ≤ n := by
  obtain ⟨cols, _⟩ := hfull
  simpa using Fintype.card_le_of_injective cols cols.injective

/-- Full row rank forces the canonical simplification to contain at least three classes. -/
theorem three_le_simplificationSize_of_hasFullRowRank
    {A : Matrix (Fin 3) (Fin n) ℝ} (hTwo : TNUpTo A 2) (hfull : HasFullRowRank A) :
    3 ≤ simplificationSize A := by
  have hfull' := (hasFullRowRank_iff_simplifiedMatrix hTwo).mp hfull
  obtain ⟨cols, _⟩ := hfull'
  simpa using Fintype.card_le_of_injective cols cols.injective

/-- In a `TN₂` Toeplitz matrix, the nonloop columns form an ordinary interval. -/
theorem rankThreeToeplitz_nonloop_interval
    (hTwo : TNUpTo (rankThreeToeplitz a) 2) {i j k : Fin n}
    (hij : i ≤ j) (hjk : j ≤ k)
    (hi : ¬IsLoop (rankThreeToeplitz a) i) (hk : ¬IsLoop (rankThreeToeplitz a) k) :
    ¬IsLoop (rankThreeToeplitz a) j := by
  rcases hij.eq_or_lt with rfl | hij
  · exact hi
  rcases hjk.eq_or_lt with rfl | hjk
  · exact hk
  have hn : 3 ≤ n := by omega
  have hcoeffNonneg : ∀ t, 0 ≤ a t := rankThreeToeplitz_coeff_nonneg (by omega) hTwo
  have hsupport : HasIntervalPositiveSupport a :=
    rankThreeToeplitz_hasIntervalPositiveSupport hn hTwo
  have hiEntry : ∃ r : Fin 3, 0 < rankThreeToeplitz a r i := by
    by_contra h
    apply hi
    rw [isLoop_iff_entry_eq_zero]
    intro r
    apply le_antisymm (le_of_not_gt (not_exists.mp h r))
    exact hTwo.entry_nonneg (by omega) r i
  have hkEntry : ∃ r : Fin 3, 0 < rankThreeToeplitz a r k := by
    by_contra h
    apply hk
    rw [isLoop_iff_entry_eq_zero]
    intro r
    apply le_antisymm (le_of_not_gt (not_exists.mp h r))
    exact hTwo.entry_nonneg (by omega) r k
  obtain ⟨ri, hri⟩ := hiEntry
  obtain ⟨rk, hrk⟩ := hkEntry
  have hiCoeff : ∃ t : Fin (n + 2), 0 < a t ∧ t.val ≤ j.val + 1 := by
    fin_cases ri
    · refine ⟨i.succ.succ, ?_, ?_⟩
      · exact hri
      · simp; omega
    · refine ⟨i.succ.castSucc, ?_, ?_⟩
      · exact hri
      · simp; omega
    · refine ⟨i.castSucc.castSucc, ?_, ?_⟩
      · exact hri
      · simp; omega
  have hkCoeff : ∃ t : Fin (n + 2), 0 < a t ∧ j.val + 1 ≤ t.val := by
    fin_cases rk
    · refine ⟨k.succ.succ, ?_, ?_⟩
      · exact hrk
      · simp; omega
    · refine ⟨k.succ.castSucc, ?_, ?_⟩
      · exact hrk
      · simp; omega
    · refine ⟨k.castSucc.castSucc, ?_, ?_⟩
      · exact hrk
      · simp; omega
  obtain ⟨u, hu, huj⟩ := hiCoeff
  obtain ⟨v, hv, hjv⟩ := hkCoeff
  let center : Fin (n + 2) := ⟨j.val + 1, by omega⟩
  have hcenter : 0 < a center :=
    (hasIntervalPositiveSupport_iff a).mp hsupport u v center hu hv
      (by apply Fin.mk_le_mk.mpr; exact huj)
      (by apply Fin.mk_le_mk.mpr; exact hjv)
  intro hjLoop
  have hjZero := isLoop_iff_entry_eq_zero.mp hjLoop (1 : Fin 3)
  change a center = 0 at hjZero
  linarith

/-- The finite set of nonloop column indices. -/
def nonloopIndices (A : Matrix (Fin 3) (Fin n) ℝ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ ¬IsLoop A j

@[simp]
theorem mem_nonloopIndices {A : Matrix (Fin 3) (Fin n) ℝ} {j : Fin n} :
    j ∈ nonloopIndices A ↔ ¬IsLoop A j := by
  classical
  simp [nonloopIndices]

theorem nonloopIndices_nonempty {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A) :
    (nonloopIndices A).Nonempty := by
  obtain ⟨cols, hcols⟩ := hfull
  refine ⟨cols 0, ?_⟩
  rw [mem_nonloopIndices]
  intro hloop
  exact hcols (orderedMinor_allRows_eq_zero_of_isLoop A cols 0 hloop)

/-- The final nonloop column, defined canonically as the maximum nonloop index. -/
def lastNonloopIndex (A : Matrix (Fin 3) (Fin n) ℝ) (hfull : HasFullRowRank A) : Fin n :=
  (nonloopIndices A).max' (nonloopIndices_nonempty hfull)

theorem lastNonloopIndex_nonloop (A : Matrix (Fin 3) (Fin n) ℝ)
    (hfull : HasFullRowRank A) :
    ¬IsLoop A (lastNonloopIndex A hfull) := by
  exact mem_nonloopIndices.mp (Finset.max'_mem _ _)

theorem nonloop_le_lastNonloopIndex {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A) {j : Fin n} (hj : ¬IsLoop A j) :
    j ≤ lastNonloopIndex A hfull := by
  exact Finset.le_max' _ j (mem_nonloopIndices.mpr hj)

/-- Every column after the final nonloop column is a loop. -/
theorem isLoop_of_lastNonloopIndex_lt {A : Matrix (Fin 3) (Fin n) ℝ}
    (hfull : HasFullRowRank A) {j : Fin n} (hj : lastNonloopIndex A hfull < j) :
    IsLoop A j := by
  by_contra hjNonloop
  exact (not_le_of_gt hj) (nonloop_le_lastNonloopIndex hfull hjNonloop)

/-- The first simplification representative is no later than every nonloop column. -/
theorem first_simplificationEmbedding_le_nonloop
    {A : Matrix (Fin 3) (Fin n) ℝ} (hm : 0 < simplificationSize A)
    {j : Fin n} (hj : ¬IsLoop A j) :
    simplificationEmbedding A ⟨0, hm⟩ ≤ j := by
  rcases exists_simplificationEmbedding_eq_parallelRepresentative A hj with ⟨p, hp⟩
  have hfirst : simplificationEmbedding A ⟨0, hm⟩ ≤ simplificationEmbedding A p :=
    (simplificationEmbedding A).monotone (Fin.mk_le_mk.mpr (Nat.zero_le _))
  rw [hp] at hfirst
  exact hfirst.trans (parallelRepresentative_le (columnsPositivelyParallel_refl A j))

/-- Every column before the first simplification representative is a loop. -/
theorem isLoop_of_lt_first_simplificationEmbedding
    {A : Matrix (Fin 3) (Fin n) ℝ} (hm : 0 < simplificationSize A)
    {j : Fin n} (hj : j < simplificationEmbedding A ⟨0, hm⟩) :
    IsLoop A j := by
  by_contra hjNonloop
  exact (not_le_of_gt hj) (first_simplificationEmbedding_le_nonloop hm hjNonloop)

/-- Every nonloop column before the second representative belongs to the initial parallel
class. -/
theorem columnsPositivelyParallel_first_of_lt_secondRepresentative
    {A : Matrix (Fin 3) (Fin n) ℝ} (hm : 2 ≤ simplificationSize A)
    {j : Fin n}
    (hjsecond : j < simplificationEmbedding A ⟨1, by omega⟩) (hj : ¬IsLoop A j) :
    ColumnsPositivelyParallel A (simplificationEmbedding A ⟨0, by omega⟩) j := by
  let c := simplificationClassIndex A j hj
  have hc_lt_one : c < (⟨1, by omega⟩ : Fin (simplificationSize A)) := by
    by_contra hc
    have honec : (⟨1, by omega⟩ : Fin (simplificationSize A)) ≤ c := le_of_not_gt hc
    have hemb := (simplificationEmbedding A).monotone honec
    have hrep := simplificationEmbedding_classIndex_eq_parallelRepresentative A j hj
    have hrepLe : parallelRepresentative A j ≤ j :=
      parallelRepresentative_le (columnsPositivelyParallel_refl A j)
    rw [← hrep] at hrepLe
    exact (not_le_of_gt hjsecond) (hemb.trans hrepLe)
  have hcZero : c = ⟨0, by omega⟩ := by
    change c.val < 1 at hc_lt_one
    apply Fin.ext
    change c.val = 0
    omega
  have hpar := simplificationClassIndex_parallel A j hj
  simpa [c, hcZero] using hpar

/-- Every nonloop column from the last representative onward belongs to the terminal parallel
class. -/
theorem columnsPositivelyParallel_last_of_lastRepresentative_le
    {A : Matrix (Fin 3) (Fin n) ℝ} (hTwo : TNUpTo A 2) (hm : 0 < simplificationSize A)
    {j : Fin n}
    (hlastj : simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩ ≤ j)
    (hj : ¬IsLoop A j) :
    ColumnsPositivelyParallel A
      (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩) j := by
  let c := simplificationClassIndex A j hj
  have hlast_le_c := simplificationClassIndex_mono_of_tnUpTo_two hTwo hlastj
    (simplificationEmbedding_not_isLoop A _) hj
  have hclassLast :
      simplificationClassIndex A
          (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩)
          (simplificationEmbedding_not_isLoop A _) =
        ⟨simplificationSize A - 1, by omega⟩ := by
    apply (simplificationClassIndex_eq_iff A _ _ _).mpr
    exact columnsPositivelyParallel_refl A _
  rw [hclassLast] at hlast_le_c
  change (⟨simplificationSize A - 1, by omega⟩ : Fin (simplificationSize A)) ≤ c at hlast_le_c
  have hcLast : c = ⟨simplificationSize A - 1, by omega⟩ := by
    apply Fin.ext
    apply Nat.le_antisymm
    · exact Nat.le_sub_one_of_lt c.isLt
    · exact Fin.mk_le_mk.mp hlast_le_c
  have hpar := simplificationClassIndex_parallel A j hj
  simpa [c, hcLast] using hpar

/-- Consecutive internal simplification representatives are consecutive raw columns.  This is
the endpoint-parallel theorem in the form needed by the canonical block decomposition. -/
theorem rankThreeToeplitz_internal_representatives_consecutive
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    {q : Fin (simplificationSize (rankThreeToeplitz a))} (hqPos : 0 < q.val)
    (hqNext : q.val + 1 < simplificationSize (rankThreeToeplitz a)) :
    (simplificationEmbedding (rankThreeToeplitz a) ⟨q.val + 1, hqNext⟩).val =
      (simplificationEmbedding (rankThreeToeplitz a) q).val + 1 := by
  let A := rankThreeToeplitz a
  let qnext : Fin (simplificationSize A) := ⟨q.val + 1, hqNext⟩
  let first : Fin n := simplificationEmbedding A q
  let next : Fin n := simplificationEmbedding A qnext
  let p := first.val
  let L := next.val - first.val
  change q.val + 1 < simplificationSize A at hqNext
  have hq_lt_next : q < qnext := by
    apply Fin.mk_lt_mk.mpr
    simp
  have hfirstNext : first < next := (simplificationEmbedding A).strictMono hq_lt_next
  have hfirstNextVal : first.val < next.val := hfirstNext
  by_contra hgap
  have hgap' : next.val ≠ first.val + 1 := by
    simpa [A, qnext, first, next] using hgap
  have hL : 2 ≤ L := by
    dsimp [L]
    omega
  have hp : 1 ≤ p := by
    have hm : 0 < simplificationSize A := lt_of_le_of_lt (Nat.zero_le _) hqNext
    have hzeroq : (⟨0, hm⟩ : Fin (simplificationSize A)) < q := by
      apply Fin.mk_lt_mk.mpr
      exact hqPos
    have := (simplificationEmbedding A).strictMono hzeroq
    change (simplificationEmbedding A ⟨0, hm⟩).val < p at this
    omega
  have hbound : p + L < n := by
    have hpL : p + L = next.val := by
      dsimp [p, L]
      omega
    rw [hpL]
    exact next.isLt
  have hTwo : TNUpTo A 2 := hTN.tnUpTo 2
  have hfirstNonloop : ¬IsLoop A first := simplificationEmbedding_not_isLoop A q
  have hnextNonloop : ¬IsLoop A next := simplificationEmbedding_not_isLoop A qnext
  have hblock : ∀ t : Fin L,
      ColumnsPositivelyParallel A first ⟨p + t.val, by omega⟩ := by
    intro t
    let x : Fin n := ⟨p + t.val, by omega⟩
    have hfirstx : first ≤ x := by
      apply Fin.mk_le_mk.mpr
      change p ≤ p + t.val
      exact Nat.le_add_right _ _
    have hxnext : x < next := by
      apply Fin.mk_lt_mk.mpr
      change p + t.val < next.val
      have ht := t.isLt
      dsimp [L, p] at ht
      omega
    have hxNonloop : ¬IsLoop A x := by
      exact rankThreeToeplitz_nonloop_interval hTwo hfirstx hxnext.le
        hfirstNonloop hnextNonloop
    let c := simplificationClassIndex A x hxNonloop
    have hclassFirst : simplificationClassIndex A first hfirstNonloop = q := by
      apply (simplificationClassIndex_eq_iff A first hfirstNonloop q).mpr
      simpa [first] using columnsPositivelyParallel_refl A first
    have hq_le_c : q ≤ c := by
      have hmono :=
        simplificationClassIndex_mono_of_tnUpTo_two hTwo hfirstx hfirstNonloop hxNonloop
      rw [hclassFirst] at hmono
      exact hmono
    have hc_lt_next : c < qnext := by
      by_contra hc
      have hnextc : qnext ≤ c := le_of_not_gt hc
      have hemb := (simplificationEmbedding A).monotone hnextc
      have hrep := simplificationEmbedding_classIndex_eq_parallelRepresentative A x hxNonloop
      have hrepLe : parallelRepresentative A x ≤ x :=
        parallelRepresentative_le (columnsPositivelyParallel_refl A x)
      rw [← hrep] at hrepLe
      exact (not_le_of_gt hxnext) (hemb.trans hrepLe)
    have hcq : c = q := by
      apply Fin.ext
      change c.val = q.val
      have hqv : q.val ≤ c.val := hq_le_c
      have hcv : c.val < q.val + 1 := by
        exact Fin.mk_lt_mk.mp hc_lt_next
      omega
    have hcpar := simplificationClassIndex_parallel A x hxNonloop
    simpa [c, hcq, first, x] using hcpar
  have hendpoints : ColumnsParallel A ⟨p, by omega⟩ ⟨p + L - 1, by omega⟩ := by
    have hlastPar := hblock ⟨L - 1, by omega⟩
    have hlastPar' : ColumnsPositivelyParallel A first ⟨p + L - 1, by omega⟩ := by
      convert hlastPar using 1
      apply Fin.ext
      simp
      omega
    have hlastNonloop : ¬IsLoop A ⟨p + L - 1, by omega⟩ := by
      intro hlast
      exact hfirstNonloop ((isLoop_iff_of_columnsPositivelyParallel hlastPar').mpr hlast)
    refine ⟨by simpa [p, first] using hfirstNonloop, ?_⟩
    simpa [p, first] using hlastPar'
  have hnonloop : ∀ t : Fin L, ¬IsLoop A ⟨p + t, by omega⟩ := by
    intro t ht
    exact hfirstNonloop ((isLoop_iff_of_columnsPositivelyParallel (hblock t)).mpr ht)
  have hleftMaximal :
      ¬ColumnsPositivelyParallel A ⟨p - 1, by omega⟩ ⟨p, by omega⟩ := by
    intro hpar
    have hrepEq := parallelRepresentative_eq_iff.mpr hpar
    have hpFixed : parallelRepresentative A ⟨p, by omega⟩ = ⟨p, by omega⟩ := by
      simpa [p, first] using parallelRepresentative_simplificationEmbedding A q
    rw [hpFixed] at hrepEq
    have hrepLe : parallelRepresentative A ⟨p - 1, by omega⟩ ≤ ⟨p - 1, by omega⟩ :=
      parallelRepresentative_le (columnsPositivelyParallel_refl A _)
    rw [hrepEq] at hrepLe
    exact (not_le_of_gt (show (⟨p - 1, by omega⟩ : Fin n) < ⟨p, by omega⟩ by
      apply Fin.mk_lt_mk.mpr
      omega)) hrepLe
  have hrightMaximal :
      ¬ColumnsPositivelyParallel A ⟨p + L - 1, by omega⟩ ⟨p + L, by omega⟩ := by
    intro hpar
    have hlastPar := hblock ⟨L - 1, by omega⟩
    have hlastPar' : ColumnsPositivelyParallel A first ⟨p + L - 1, by omega⟩ := by
      convert hlastPar using 1
      apply Fin.ext
      simp
      omega
    have hfirstNextPar := columnsPositivelyParallel_trans hlastPar' hpar
    have hpLEq : (⟨p + L, by omega⟩ : Fin n) = next := by
      apply Fin.ext
      dsimp [p, L]
      omega
    rw [hpLEq] at hfirstNextPar
    have hclasses := (simplificationEmbedding_parallel_iff A (p := q) (q := qnext)).mp (by
      simpa [first, next] using hfirstNextPar)
    exact (ne_of_lt hq_lt_next) hclasses
  let block : IsMaximalParallelBlock A p L :=
    { two_le := hL
      bound := hbound.le
      nonloop := hnonloop
      parallel := hblock
      left_maximal := fun _ ↦ hleftMaximal
      right_maximal := fun _ ↦ hrightMaximal }
  rcases rankThreeToeplitz_endpointParallel hTN (by simpa [A] using block) with hp0 | hterminal
  · omega
  · omega

/-- The increasing embedding of the first three indices into a finite order of size at least
three. -/
def firstThreeEmbedding {m : ℕ} (hm : 3 ≤ m) : Fin 3 ↪o Fin m :=
  selectedTripleEmbedding ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- The increasing embedding of the last three indices into a finite order of size at least
three. -/
def lastThreeEmbedding {m : ℕ} (hm : 3 ≤ m) : Fin 3 ↪o Fin m :=
  selectedTripleEmbedding ⟨m - 3, by omega⟩ ⟨m - 2, by omega⟩ ⟨m - 1, by omega⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- A finite presentation of simplified intervals by their ordered endpoint pairs. -/
def simplifiedIntervalEquiv (m : ℕ) :
    SimplifiedInterval m ≃ {p : Fin m × Fin m // p.1 ≤ p.2} where
  toFun H := ⟨(H.left, H.right), H.left_le_right⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv H := by cases H; rfl
  right_inv p := by cases p; rfl

noncomputable instance simplifiedIntervalFintype (m : ℕ) : Fintype (SimplifiedInterval m) :=
  Fintype.ofEquiv {p : Fin m × Fin m // p.1 ≤ p.2} (simplifiedIntervalEquiv m).symm

/-- A simplified interval is canonical for `A` when its endpoints are those of a maximal
constant-slope interval. -/
def IsCanonicalCollinearInterval (A : Matrix (Fin 3) (Fin n) ℝ)
    (H : SimplifiedInterval (simplificationSize A)) : Prop :=
  ∃ I : MaximalConstantSlopeInterval A,
    I.start = H.left.val ∧ I.stop = H.right.val

/-- The finite family of maximal collinear intervals of the canonical simplification. -/
noncomputable def canonicalCollinearIntervals
    (A : Matrix (Fin 3) (Fin n) ℝ) :
    Finset (SimplifiedInterval (simplificationSize A)) := by
  classical
  exact Finset.univ.filter (IsCanonicalCollinearInterval A)

@[simp]
theorem mem_canonicalCollinearIntervals {A : Matrix (Fin 3) (Fin n) ℝ}
    {H : SimplifiedInterval (simplificationSize A)} :
    H ∈ canonicalCollinearIntervals A ↔
      ∃ I : MaximalConstantSlopeInterval A,
        I.start = H.left.val ∧ I.stop = H.right.val := by
  classical
  simp [canonicalCollinearIntervals, IsCanonicalCollinearInterval]

/-- Every canonical collinear interval contains at least three simplified vertices. -/
theorem canonicalCollinearInterval_large {A : Matrix (Fin 3) (Fin n) ℝ}
    {H : SimplifiedInterval (simplificationSize A)}
    (hH : H ∈ canonicalCollinearIntervals A) :
    H.left.val + 2 ≤ H.right.val := by
  rcases mem_canonicalCollinearIntervals.mp hH with ⟨I, hleft, hright⟩
  have hlarge := I.nontrivial
  omega

/-- Distinct canonical collinear intervals are disjoint or meet at one common endpoint. -/
theorem canonicalCollinearIntervals_separated {A : Matrix (Fin 3) (Fin n) ℝ}
    {H K : SimplifiedInterval (simplificationSize A)}
    (hH : H ∈ canonicalCollinearIntervals A)
    (hK : K ∈ canonicalCollinearIntervals A) (hHK : H ≠ K) :
    H.right < K.left ∨ K.right < H.left ∨ H.right = K.left ∨ K.right = H.left := by
  rcases mem_canonicalCollinearIntervals.mp hH with ⟨I, hIl, hIr⟩
  rcases mem_canonicalCollinearIntervals.mp hK with ⟨J, hJl, hJr⟩
  have hHle := H.left_le_right
  have hKle := K.left_le_right
  have hIJ : I ≠ J := by
    intro hEq
    subst J
    apply hHK
    have hl : H.left = K.left := by apply Fin.ext; omega
    have hr : H.right = K.right := by apply Fin.ext; omega
    cases H
    cases K
    simp_all
  by_cases hsep : H.right < K.left
  · exact Or.inl hsep
  by_cases hsep' : K.right < H.left
  · exact Or.inr (Or.inl hsep')
  have hKlHr : K.left.val ≤ H.right.val := by
    have := not_lt.mp hsep
    exact this
  have hHlKr : H.left.val ≤ K.right.val := by
    have := not_lt.mp hsep'
    exact this
  by_cases hle : H.left ≤ K.left
  · have hxI : K.left.val ∈ I.vertices := by
      rw [MaximalConstantSlopeInterval.mem_vertices]
      exact ⟨by omega, by omega⟩
    have hxJ : K.left.val ∈ J.vertices := by
      rw [MaximalConstantSlopeInterval.mem_vertices]
      exact ⟨by omega, by omega⟩
    rcases MaximalConstantSlopeInterval.common_vertex_is_common_endpoint hIJ hxI hxJ with
      htouch | htouch
    · exact Or.inr (Or.inr (Or.inl (by apply Fin.ext; omega)))
    · exact Or.inr (Or.inr (Or.inr (by apply Fin.ext; omega)))
  · have hle' : K.left ≤ H.left := le_of_not_ge hle
    have hxI : H.left.val ∈ I.vertices := by
      rw [MaximalConstantSlopeInterval.mem_vertices]
      exact ⟨by omega, by omega⟩
    have hxJ : H.left.val ∈ J.vertices := by
      rw [MaximalConstantSlopeInterval.mem_vertices]
      exact ⟨by omega, by omega⟩
    rcases MaximalConstantSlopeInterval.common_vertex_is_common_endpoint hIJ hxI hxJ with
      htouch | htouch
    · exact Or.inr (Or.inr (Or.inl (by apply Fin.ext; omega)))
    · exact Or.inr (Or.inr (Or.inr (by apply Fin.ext; omega)))

/-- Full row rank excludes a canonical collinear interval equal to the whole simplified set. -/
theorem canonicalCollinearInterval_not_whole {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTwo : TNUpTo A 2) (hfull : HasFullRowRank A)
    (hSlopes : SimplifiedSlopesMonotone A)
    {H : SimplifiedInterval (simplificationSize A)}
    (hH : H ∈ canonicalCollinearIntervals A) :
    H.left.val ≠ 0 ∨ H.right.val + 1 ≠ simplificationSize A := by
  by_contra h
  push Not at h
  rcases mem_canonicalCollinearIntervals.mp hH with ⟨I, hleft, hright⟩
  have hwhole : WholeSimplifiedChainIsOneRun A := by
    refine ⟨I, ?_, ?_⟩ <;> omega
  have hsize := three_le_simplificationSize_of_hasFullRowRank hTwo hfull
  have hnotFull :=
    (wholeSimplifiedChainIsOneRun_iff_not_hasFullRowRank hTwo hSlopes hsize).mp hwhole
  exact hnotFull hfull

/-- A positive first simplified maximal minor excludes the first vertex from every canonical
collinear interval. -/
theorem canonicalCollinearInterval_left_protected {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTwo : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    (hm : 3 ≤ simplificationSize A)
    (hpos : 0 < orderedMinor (simplifiedMatrix A) (allRows 3) (firstThreeEmbedding hm))
    {H : SimplifiedInterval (simplificationSize A)}
    (hH : H ∈ canonicalCollinearIntervals A) :
    H.left.val ≠ 0 := by
  intro hleft
  rcases mem_canonicalCollinearIntervals.mp hH with ⟨I, hIl, hIr⟩
  have hIstart : I.start = 0 := hIl.trans hleft
  have hIstop : 2 ≤ I.stop := by
    have := I.nontrivial
    omega
  have hconstant :
      SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) 0 2 := by
    intro t ht ht2
    have hI := I.constant (t := t) (by omega) (by omega)
    have hI0 := I.constant (t := 0) (by omega) (by omega)
    exact hI.trans hI0.symm
  have hzero : orderedMinor (simplifiedMatrix A) (allRows 3) (firstThreeEmbedding hm) = 0 := by
    unfold firstThreeEmbedding
    apply (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hTwo hSlopes
      (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))).mpr
    exact hconstant
  linarith

/-- A positive last simplified maximal minor excludes the last vertex from every canonical
collinear interval. -/
theorem canonicalCollinearInterval_right_protected {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTwo : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    (hm : 3 ≤ simplificationSize A)
    (hpos : 0 < orderedMinor (simplifiedMatrix A) (allRows 3) (lastThreeEmbedding hm))
    {H : SimplifiedInterval (simplificationSize A)}
    (hH : H ∈ canonicalCollinearIntervals A) :
    H.right.val + 1 ≠ simplificationSize A := by
  intro hright
  rcases mem_canonicalCollinearIntervals.mp hH with ⟨I, hIl, hIr⟩
  let p : Fin (simplificationSize A) := ⟨simplificationSize A - 3, by omega⟩
  let q : Fin (simplificationSize A) := ⟨simplificationSize A - 2, by omega⟩
  let r : Fin (simplificationSize A) := ⟨simplificationSize A - 1, by omega⟩
  have hqr : q < r := by
    apply Fin.mk_lt_mk.mpr
    change simplificationSize A - 2 < simplificationSize A - 1
    omega
  have hpq : p < q := by
    apply Fin.mk_lt_mk.mpr
    change simplificationSize A - 3 < simplificationSize A - 2
    omega
  have hIstop : I.stop = simplificationSize A - 1 := by omega
  have hIstart : I.start ≤ simplificationSize A - 3 := by
    have := I.nontrivial
    omega
  have hconstant :
      SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) p.val r.val := by
    intro t ht htr
    have hI := I.constant (t := t) (by exact hIstart.trans ht) (by omega)
    have hIp := I.constant (t := p.val) hIstart (by omega)
    exact hI.trans hIp.symm
  have hzero : orderedMinor (simplifiedMatrix A) (allRows 3) (lastThreeEmbedding hm) = 0 := by
    unfold lastThreeEmbedding
    exact (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hTwo hSlopes hpq hqr).mpr
      hconstant
  linarith

/-- The raw block represented by the first simplified class is a maximal parallel block when it
is nontrivial. -/
theorem initialClass_isMaximalParallelBlock
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hm : 3 ≤ simplificationSize (rankThreeToeplitz a))
    (hlarge : 2 ≤ (simplificationEmbedding (rankThreeToeplitz a) ⟨1, by omega⟩).val -
      (simplificationEmbedding (rankThreeToeplitz a) ⟨0, by omega⟩).val) :
    IsMaximalParallelBlock (rankThreeToeplitz a)
      (simplificationEmbedding (rankThreeToeplitz a) ⟨0, by omega⟩).val
      ((simplificationEmbedding (rankThreeToeplitz a) ⟨1, by omega⟩).val -
        (simplificationEmbedding (rankThreeToeplitz a) ⟨0, by omega⟩).val) := by
  let A := rankThreeToeplitz a
  change 3 ≤ simplificationSize A at hm
  let first : Fin n := simplificationEmbedding A ⟨0, by omega⟩
  let second : Fin n := simplificationEmbedding A ⟨1, by omega⟩
  let p := first.val
  let L := second.val - first.val
  change 2 ≤ L at hlarge
  have hfirstSecond : first < second := (simplificationEmbedding A).strictMono
    (Fin.mk_lt_mk.mpr (by norm_num))
  have hpL : p + L = second.val := by dsimp [p, L]; omega
  have hBlockBound : p + L ≤ n := hpL.symm ▸ second.isLt.le
  have hTwo : TNUpTo A 2 := hTN.tnUpTo 2
  refine
    { two_le := hlarge
      bound := hBlockBound
      nonloop := ?_
      parallel := ?_
      left_maximal := ?_
      right_maximal := ?_ }
  · intro t
    have hjBound : p + t.val < n :=
      (Nat.add_lt_add_left t.isLt p).trans_le hBlockBound
    let j : Fin n := ⟨p + t.val, hjBound⟩
    have hfirstj : first ≤ j := by apply Fin.mk_le_mk.mpr; change p ≤ p + t.val; omega
    have hjsecond : j < second := by
      apply Fin.mk_lt_mk.mpr
      change p + t.val < second.val
      have ht := t.isLt
      change t.val < L at ht
      omega
    exact rankThreeToeplitz_nonloop_interval hTwo hfirstj hjsecond.le
      (simplificationEmbedding_not_isLoop A _) (simplificationEmbedding_not_isLoop A _)
  · intro t
    have hjBound : p + t.val < n :=
      (Nat.add_lt_add_left t.isLt p).trans_le hBlockBound
    let j : Fin n := ⟨p + t.val, hjBound⟩
    have hjsecond : j < second := by
      apply Fin.mk_lt_mk.mpr
      change p + t.val < second.val
      have ht := t.isLt
      change t.val < L at ht
      omega
    have hjNonloop := rankThreeToeplitz_nonloop_interval hTwo (by
      apply Fin.mk_le_mk.mpr; change p ≤ p + t.val; omega) hjsecond.le
      (simplificationEmbedding_not_isLoop A _) (simplificationEmbedding_not_isLoop A _)
    simpa [first, j] using
      columnsPositivelyParallel_first_of_lt_secondRepresentative (A := A) (by omega)
        hjsecond hjNonloop
  · intro hp
    change 1 ≤ p at hp
    have hloop : IsLoop A ⟨p - 1, by omega⟩ := by
      apply isLoop_of_lt_first_simplificationEmbedding (A := A) (by omega)
      apply Fin.mk_lt_mk.mpr
      change p - 1 < p
      omega
    intro hpar
    exact (simplificationEmbedding_not_isLoop A _)
      ((isLoop_iff_of_columnsPositivelyParallel hpar).mp hloop)
  · intro hright
    have hindex : (⟨p + L, hright⟩ : Fin n) = second := Fin.ext hpL
    rw [hindex]
    intro hpar
    have hlastNonloop : ¬IsLoop A ⟨p + L - 1, by omega⟩ := by
      exact rankThreeToeplitz_nonloop_interval hTwo (by
        apply Fin.mk_le_mk.mpr; change p ≤ p + L - 1; omega) (by
        apply Fin.mk_le_mk.mpr; change p + L - 1 ≤ second.val; rw [← hpL]; omega)
        (simplificationEmbedding_not_isLoop A _)
        (simplificationEmbedding_not_isLoop A _)
    have hfirstLast := columnsPositivelyParallel_first_of_lt_secondRepresentative
      (A := A) (by omega) (j := ⟨p + L - 1, by omega⟩) (by
        apply Fin.mk_lt_mk.mpr; change p + L - 1 < second.val; rw [← hpL]; omega) hlastNonloop
    have hfirstSecond := columnsPositivelyParallel_trans hfirstLast hpar
    have hclasses := (simplificationEmbedding_parallel_iff A
      (p := (⟨0, by omega⟩ : Fin (simplificationSize A)))
      (q := ⟨1, by omega⟩)).mp (by simpa [first, second] using hfirstSecond)
    norm_num at hclasses

/-- The raw block represented by the last simplified class is a maximal parallel block when it
is nontrivial. -/
theorem terminalClass_isMaximalParallelBlock
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (hm : 3 ≤ simplificationSize (rankThreeToeplitz a))
    (hlarge : 2 ≤ (lastNonloopIndex (rankThreeToeplitz a) hfull).val + 1 -
      (simplificationEmbedding (rankThreeToeplitz a)
        ⟨simplificationSize (rankThreeToeplitz a) - 1, by omega⟩).val) :
    IsMaximalParallelBlock (rankThreeToeplitz a)
      (simplificationEmbedding (rankThreeToeplitz a)
        ⟨simplificationSize (rankThreeToeplitz a) - 1, by omega⟩).val
      ((lastNonloopIndex (rankThreeToeplitz a) hfull).val + 1 -
        (simplificationEmbedding (rankThreeToeplitz a)
          ⟨simplificationSize (rankThreeToeplitz a) - 1, by omega⟩).val) := by
  let A := rankThreeToeplitz a
  change 3 ≤ simplificationSize A at hm
  let q : Fin (simplificationSize A) := ⟨simplificationSize A - 1, by omega⟩
  let first : Fin n := simplificationEmbedding A q
  let last := lastNonloopIndex A hfull
  let p := first.val
  let L := last.val + 1 - first.val
  change 2 ≤ L at hlarge
  have hfirstLast : first ≤ last := nonloop_le_lastNonloopIndex hfull
    (simplificationEmbedding_not_isLoop A _)
  have hpL : p + L = last.val + 1 := by dsimp [p, L]; omega
  have hBlockBound : p + L ≤ n := by rw [hpL]; exact last.isLt
  have hTwo : TNUpTo A 2 := hTN.tnUpTo 2
  refine
    { two_le := hlarge
      bound := hBlockBound
      nonloop := ?_
      parallel := ?_
      left_maximal := ?_
      right_maximal := ?_ }
  · intro t
    have hjBound : p + t.val < n :=
      (Nat.add_lt_add_left t.isLt p).trans_le hBlockBound
    let j : Fin n := ⟨p + t.val, hjBound⟩
    have hfirstj : first ≤ j := by apply Fin.mk_le_mk.mpr; change p ≤ p + t.val; omega
    have hjlast : j ≤ last := by
      apply Fin.mk_le_mk.mpr
      change p + t.val ≤ last.val
      have ht := t.isLt
      change t.val < L at ht
      omega
    exact rankThreeToeplitz_nonloop_interval hTwo hfirstj hjlast
      (simplificationEmbedding_not_isLoop A _) (lastNonloopIndex_nonloop A hfull)
  · intro t
    have hjBound : p + t.val < n :=
      (Nat.add_lt_add_left t.isLt p).trans_le hBlockBound
    let j : Fin n := ⟨p + t.val, hjBound⟩
    have hfirstj : first ≤ j := by apply Fin.mk_le_mk.mpr; change p ≤ p + t.val; omega
    have hjlast : j ≤ last := by
      apply Fin.mk_le_mk.mpr
      change p + t.val ≤ last.val
      have ht := t.isLt
      change t.val < L at ht
      omega
    have hjNonloop := rankThreeToeplitz_nonloop_interval hTwo hfirstj hjlast
      (simplificationEmbedding_not_isLoop A _) (lastNonloopIndex_nonloop A hfull)
    simpa [first, j] using columnsPositivelyParallel_last_of_lastRepresentative_le
      hTwo (by omega) hfirstj hjNonloop
  · intro hp
    change 1 ≤ p at hp
    intro hpar
    have hrepEq := parallelRepresentative_eq_iff.mpr hpar
    have hpFixed : parallelRepresentative A ⟨p, by omega⟩ = ⟨p, by omega⟩ := by
      simpa [p, first, q] using parallelRepresentative_simplificationEmbedding A q
    rw [hpFixed] at hrepEq
    have hrepLe : parallelRepresentative A ⟨p - 1, by omega⟩ ≤ ⟨p - 1, by omega⟩ :=
      parallelRepresentative_le (columnsPositivelyParallel_refl A _)
    rw [hrepEq] at hrepLe
    exact (not_le_of_gt (show (⟨p - 1, by omega⟩ : Fin n) < ⟨p, by omega⟩ by
      apply Fin.mk_lt_mk.mpr; omega)) hrepLe
  · intro hright
    have hlastEq : (⟨p + L - 1, by omega⟩ : Fin n) = last := by
      apply Fin.ext
      change p + L - 1 = last.val
      omega
    rw [hlastEq]
    have hloop : IsLoop A ⟨p + L, hright⟩ := by
      apply isLoop_of_lastNonloopIndex_lt hfull
      apply Fin.mk_lt_mk.mpr
      change last.val < p + L
      omega
    intro hpar
    exact (lastNonloopIndex_nonloop A hfull)
      ((isLoop_iff_of_columnsPositivelyParallel hpar).mpr hloop)

/-- From the second simplified class onward, all representatives before the terminal class are
consecutive raw columns. -/
theorem internal_simplificationEmbedding_val
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hm : 3 ≤ simplificationSize (rankThreeToeplitz a))
    {k : ℕ} (hk1 : 1 ≤ k) (hkm : k < simplificationSize (rankThreeToeplitz a)) :
    (simplificationEmbedding (rankThreeToeplitz a) ⟨k, hkm⟩).val =
      (simplificationEmbedding (rankThreeToeplitz a) ⟨1, by omega⟩).val + (k - 1) := by
  induction k, hk1 using Nat.le_induction with
  | base => simp
  | succ k hk1 ih =>
      have hklt : k < simplificationSize (rankThreeToeplitz a) := by omega
      have hstep := rankThreeToeplitz_internal_representatives_consecutive hTN
        (q := (⟨k, hklt⟩ : Fin (simplificationSize (rankThreeToeplitz a))))
        (lt_of_lt_of_le zero_lt_one hk1) hkm
      have ih' := ih hklt
      have hstep' :
          (simplificationEmbedding (rankThreeToeplitz a) ⟨k + 1, hkm⟩).val =
            (simplificationEmbedding (rankThreeToeplitz a) ⟨k, hklt⟩).val + 1 := by
        exact hstep
      rw [hstep', ih']
      omega

/-- The canonical numerical counts extracted from a full-rank three-row matrix. -/
structure CanonicalRankThreeCounts (A : Matrix (Fin 3) (Fin n) ℝ) where
  leftLoops : ℕ
  rightLoops : ℕ
  initialClass : ℕ
  terminalClass : ℕ
  simplified : ℕ

/-- The canonical block counts of a full-rank Toeplitz configuration. -/
def canonicalRankThreeCounts
    (hTwo : TNUpTo (rankThreeToeplitz a) 2)
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    CanonicalRankThreeCounts (rankThreeToeplitz a) :=
  let A := rankThreeToeplitz a
  let m := simplificationSize A
  let hm : 3 ≤ m := three_le_simplificationSize_of_hasFullRowRank hTwo hfull
  let first := simplificationEmbedding A ⟨0, by omega⟩
  { leftLoops := first.val
    rightLoops := n - ((lastNonloopIndex A hfull).val + 1)
    initialClass := (simplificationEmbedding A ⟨1, by omega⟩).val - first.val
    terminalClass := (lastNonloopIndex A hfull).val + 1 -
      (simplificationEmbedding A ⟨m - 1, by omega⟩).val
    simplified := m }

/-- Positivity of a raw maximal minor transfers to a selected simplification triple when each
raw column is a positive multiple of the corresponding simplified column. -/
theorem orderedMinor_simplified_pos_of_positiveScalings
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (raw : Fin 3 ↪o Fin n) (selected : Fin 3 ↪o Fin (simplificationSize A))
    (hscale : ∀ r : Fin 3, ∃ c : ℝ, 0 < c ∧
      A.col (raw r) = c • (simplifiedMatrix A).col (selected r))
    (hpos : 0 < orderedMinor A (allRows 3) raw) :
    0 < orderedMinor (simplifiedMatrix A) (allRows 3) selected := by
  rcases hscale 0 with ⟨c0, hc0, h0⟩
  rcases hscale 1 with ⟨c1, hc1, h1⟩
  rcases hscale 2 with ⟨c2, hc2, h2⟩
  rw [orderedMinor_allRows_eq_threeColumnMatrix_det] at hpos ⊢
  rw [h0, h1, h2, threeColumnMatrix_det_smul] at hpos
  have hprod : 0 < c0 * c1 * c2 := mul_pos (mul_pos hc0 hc1) hc2
  nlinarith

/-- The raw column two places before the last representative is a positive multiple of the
third-from-last simplification representative. -/
theorem lastThree_firstColumn_positiveScaling
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hm : 3 ≤ simplificationSize (rankThreeToeplitz a)) :
    let A := rankThreeToeplitz a
    let q0 : Fin (simplificationSize A) := ⟨simplificationSize A - 3, by
      dsimp [A]
      omega⟩
    let q2 : Fin (simplificationSize A) := ⟨simplificationSize A - 1, by
      dsimp [A]
      omega⟩
    let p := (simplificationEmbedding A q2).val
    ∃ c : ℝ, 0 < c ∧
      A.col ⟨p - 2, by
        have hp := (simplificationEmbedding A q2).isLt
        omega⟩ = c • (simplifiedMatrix A).col q0 := by
  dsimp only
  let A := rankThreeToeplitz a
  change 3 ≤ simplificationSize A at hm
  let q0 : Fin (simplificationSize A) := ⟨simplificationSize A - 3, by omega⟩
  let q1 : Fin (simplificationSize A) := ⟨simplificationSize A - 2, by omega⟩
  let q2 : Fin (simplificationSize A) := ⟨simplificationSize A - 1, by omega⟩
  let r0 : Fin n := simplificationEmbedding A q0
  let r1 : Fin n := simplificationEmbedding A q1
  let r2 : Fin n := simplificationEmbedding A q2
  let p := r2.val
  have hq1Pos : 0 < q1.val := by change 0 < simplificationSize A - 2; omega
  have hq1Next : q1.val + 1 < simplificationSize A := by
    change (simplificationSize A - 2) + 1 < simplificationSize A
    omega
  have hr2 : r2.val = r1.val + 1 := by
    have h := rankThreeToeplitz_internal_representatives_consecutive hTN hq1Pos hq1Next
    have hindex : (⟨q1.val + 1, hq1Next⟩ : Fin (simplificationSize A)) = q2 := by
      apply Fin.ext
      change (simplificationSize A - 2) + 1 = simplificationSize A - 1
      omega
    rw [hindex] at h
    change (simplificationEmbedding A q2).val = (simplificationEmbedding A q1).val + 1 at h
    exact h
  have hr0r1 : r0 < r1 := (simplificationEmbedding A).strictMono (by
    apply Fin.mk_lt_mk.mpr
    change simplificationSize A - 3 < simplificationSize A - 2
    omega)
  have hpTwo : 2 ≤ p := by
    have hr0r1v : r0.val < r1.val := hr0r1
    dsimp [p]
    omega
  let x : Fin n := ⟨p - 2, by omega⟩
  have hr0x : r0 ≤ x := by
    apply Fin.mk_le_mk.mpr
    change r0.val ≤ p - 2
    have h01 : r0.val < r1.val := hr0r1
    have h12 : r1.val < r2.val := by omega
    dsimp [p]
    omega
  have hxr2 : x ≤ r2 := by
    apply Fin.mk_le_mk.mpr
    change p - 2 ≤ r2.val
    dsimp [p]
    exact Nat.sub_le _ _
  have hxNonloop := rankThreeToeplitz_nonloop_interval (hTN.tnUpTo 2) hr0x hxr2
    (simplificationEmbedding_not_isLoop A _) (simplificationEmbedding_not_isLoop A _)
  let cx := simplificationClassIndex A x hxNonloop
  have hq0cx := simplificationClassIndex_mono_of_tnUpTo_two (hTN.tnUpTo 2) hr0x
    (simplificationEmbedding_not_isLoop A _) hxNonloop
  have hclass0 : simplificationClassIndex A r0 (simplificationEmbedding_not_isLoop A _) = q0 := by
    apply (simplificationClassIndex_eq_iff A _ _ _).mpr
    exact columnsPositivelyParallel_refl A _
  rw [hclass0] at hq0cx
  change q0 ≤ cx at hq0cx
  have hcxq1 : cx < q1 := by
    by_contra h
    have hq1cx : q1 ≤ cx := le_of_not_gt h
    have hemb := (simplificationEmbedding A).monotone hq1cx
    have hrep := simplificationEmbedding_classIndex_eq_parallelRepresentative A x hxNonloop
    have hrepLe : parallelRepresentative A x ≤ x :=
      parallelRepresentative_le (columnsPositivelyParallel_refl A x)
    rw [← hrep] at hrepLe
    have hxr1 : x < r1 := by
      apply Fin.mk_lt_mk.mpr
      change p - 2 < r1.val
      dsimp [p]
      omega
    exact (not_le_of_gt hxr1) (hemb.trans hrepLe)
  have hcx : cx = q0 := by
    apply Fin.ext
    have hle : q0.val ≤ cx.val := hq0cx
    have hlt : cx.val < q1.val := hcxq1
    simp [q0, q1] at hle hlt ⊢
    omega
  rcases simplificationClassIndex_parallel A x hxNonloop with ⟨c, hc, hscale⟩
  refine ⟨c, hc, ?_⟩
  simpa [A, x, p, cx, hcx] using hscale

/-- The canonical compatible data extracted from a full-row-rank totally nonnegative
rank-three Toeplitz matrix. -/
noncomputable def canonicalCompatibleRankThreeData
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    CompatibleRankThreeData n := by
  let A := rankThreeToeplitz a
  have hTwo : TNUpTo A 2 := hTN.tnUpTo 2
  have hm : 3 ≤ simplificationSize A :=
    three_le_simplificationSize_of_hasFullRowRank hTwo hfull
  have hSlopes : SimplifiedSlopesMonotone A :=
    (totallyNonnegative_iff_tnUpTo_two_and_simplifiedSlopesMonotone A).mp hTN |>.2
  let r0 : Fin n := simplificationEmbedding A ⟨0, by omega⟩
  let r1 : Fin n := simplificationEmbedding A ⟨1, by omega⟩
  let r2 : Fin n := simplificationEmbedding A ⟨2, by omega⟩
  let rLast : Fin n :=
    simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩
  let rPrev : Fin n :=
    simplificationEmbedding A ⟨simplificationSize A - 2, by omega⟩
  let z := lastNonloopIndex A hfull
  let leftLoops := r0.val
  let rightLoops := n - (z.val + 1)
  let initialSize := r1.val - r0.val
  let terminalSize := z.val + 1 - rLast.val
  let m := simplificationSize A
  change 3 ≤ m at hm
  have hr0r1 : r0 < r1 := (simplificationEmbedding A).strictMono
    (Fin.mk_lt_mk.mpr (by norm_num))
  have hr2Formula : r2.val = r1.val + 1 := by
    have hqNext : (1 : ℕ) + 1 < simplificationSize A := by omega
    have h := rankThreeToeplitz_internal_representatives_consecutive hTN
      (q := (⟨1, by omega⟩ : Fin (simplificationSize A))) (by norm_num) hqNext
    simpa [A, r1, r2] using h
  have hrLastPrev : rLast.val = rPrev.val + 1 := by
    have hqPos : 0 < simplificationSize A - 2 := by omega
    have hqNext : (simplificationSize A - 2) + 1 < simplificationSize A := by omega
    have h := rankThreeToeplitz_internal_representatives_consecutive hTN
      (q := (⟨simplificationSize A - 2, by omega⟩ : Fin (simplificationSize A)))
      hqPos hqNext
    have hindex :
        (⟨(simplificationSize A - 2) + 1, hqNext⟩ : Fin (simplificationSize A)) =
          ⟨simplificationSize A - 1, by omega⟩ := by
      apply Fin.ext
      change (simplificationSize A - 2) + 1 = simplificationSize A - 1
      omega
    rw [hindex] at h
    simpa [A, rPrev, rLast] using h
  have hInitialPos : 0 < initialSize := by dsimp [initialSize]; omega
  have hrLastz : rLast ≤ z := nonloop_le_lastNonloopIndex hfull
    (simplificationEmbedding_not_isLoop A _)
  have hTerminalPos : 0 < terminalSize := by dsimp [terminalSize]; omega
  have hrLastFormula : rLast.val = r1.val + (m - 2) := by
    have h := internal_simplificationEmbedding_val hTN hm
      (k := m - 1) (show 1 ≤ m - 1 by omega)
      (show m - 1 < simplificationSize (rankThreeToeplitz a) by
        change m - 1 < m
        omega)
    simpa [A, r1, rLast, m] using h
  have hGround : leftLoops + initialSize + (m - 2) + terminalSize + rightLoops = n := by
    have hzBound := z.isLt
    dsimp [leftLoops, initialSize, terminalSize, rightLoops]
    omega
  have hInitialSingleton : 0 < leftLoops → initialSize = 1 := by
    intro hleft
    by_contra hne
    have hlarge : 2 ≤ initialSize := by omega
    have hblock := initialClass_isMaximalParallelBlock hTN hm (by
      simpa [A, r0, r1, initialSize] using hlarge)
    rcases rankThreeToeplitz_endpointParallel hTN hblock with hp | hterminal
    · dsimp [leftLoops, r0] at hleft
      exact (Nat.ne_of_gt hleft) hp
    · have hr1Bound := r1.isLt
      have hterminal' : r1.val = n := by
        simpa [A, r0, r1, initialSize] using hterminal
      omega
  have hTerminalSingleton : 0 < rightLoops → terminalSize = 1 := by
    intro hright
    by_contra hne
    have hlarge : 2 ≤ terminalSize := by omega
    have hblock := terminalClass_isMaximalParallelBlock hTN hfull hm (by
      simpa [A, rLast, z, terminalSize] using hlarge)
    rcases rankThreeToeplitz_endpointParallel hTN hblock with hp | hterminal
    · have hr0Last : r0 < rLast := (simplificationEmbedding A).strictMono (by
        apply Fin.mk_lt_mk.mpr
        change 0 < m - 1
        omega)
      have hp' : rLast.val = 0 := by
        simpa [A, rLast] using hp
      omega
    · have hzBound := z.isLt
      have hterminal' : z.val + 1 = n := by
        have hraw : rLast.val + terminalSize = n := by
          simpa [A, rLast, terminalSize] using hterminal
        dsimp [terminalSize] at hraw
        omega
      dsimp [rightLoops] at hright
      omega
  have hLeftPos : 0 < leftLoops ∨ 1 < initialSize →
      0 < orderedMinor (simplifiedMatrix A) (allRows 3) (firstThreeEmbedding hm) := by
    intro hprotect
    by_cases hleft : 0 < leftLoops
    · have hp : 1 ≤ r0.val := by simpa [leftLoops] using hleft
      have hloops : ∀ j : Fin n, j.val < r0.val → IsLoop A j := by
        intro j hj
        exact isLoop_of_lt_first_simplificationEmbedding (A := A) (by omega) (by
          apply Fin.mk_lt_mk.mpr
          simpa [r0] using hj)
      obtain ⟨hbound, hrawPos, _⟩ := rankThreeToeplitz_initialLoops_endpointProtection
        hp r0.isLt hTN hfull (by simpa [A] using hloops)
        (by simpa [A, r0] using (simplificationEmbedding_not_isLoop A
          (⟨0, by omega⟩ : Fin (simplificationSize A))))
      have hinit : initialSize = 1 := hInitialSingleton hleft
      have hr1 : r1.val = r0.val + 1 := by dsimp [initialSize] at hinit; omega
      apply orderedMinor_simplified_pos_of_positiveScalings
        (A := A) (consecutiveTripleEmbedding r0.val hbound) (firstThreeEmbedding hm) _ hrawPos
      intro u
      refine ⟨1, zero_lt_one, ?_⟩
      simp only [one_smul, simplifiedMatrix_col]
      apply congrArg A.col
      fin_cases u <;> apply Fin.ext
      · simp [consecutiveTripleEmbedding, firstThreeEmbedding, r0]
      · simp [consecutiveTripleEmbedding, firstThreeEmbedding]
        omega
      · simp [consecutiveTripleEmbedding, firstThreeEmbedding]
        omega
    · have hlarge : 2 ≤ initialSize := by
        rcases hprotect with h | h
        · exact (hleft h).elim
        · omega
      have hblock := initialClass_isMaximalParallelBlock hTN hm (by
        simpa [A, r0, r1, initialSize] using hlarge)
      have hp0 : r0.val = 0 := by
        rcases rankThreeToeplitz_endpointParallel hTN hblock with hp | hterminal
        · simpa [A, r0] using hp
        · have hr1Bound := r1.isLt
          have : r1.val = n := by simpa [A, r0, r1, initialSize] using hterminal
          omega
      have hblock0 : IsMaximalParallelBlock A 0 initialSize := by
        simpa [A, r0, r1, initialSize, hp0] using hblock
      obtain ⟨hbound, hrawPos⟩ :=
        rankThreeToeplitz_initialParallel_endpointProtection hTN hfull hblock0
      have hr1 : r1.val = initialSize := by dsimp [initialSize]; omega
      apply orderedMinor_simplified_pos_of_positiveScalings
        (A := A) (consecutiveTripleEmbedding (initialSize - 1) hbound)
          (firstThreeEmbedding hm) _ hrawPos
      intro u
      fin_cases u
      · have hpar := hblock0.parallel ⟨initialSize - 1, by omega⟩
        rcases hpar with ⟨c, hc, hcol⟩
        refine ⟨c, hc, ?_⟩
        simp only [simplifiedMatrix_col]
        change A.col ⟨initialSize - 1, by omega⟩ = c • A.col r0
        have hr0Eq : r0 = (⟨0, by omega⟩ : Fin n) := Fin.ext hp0
        simpa [hr0Eq] using hcol
      · refine ⟨1, zero_lt_one, ?_⟩
        simp only [one_smul, simplifiedMatrix_col]
        apply congrArg A.col
        apply Fin.ext
        simp [consecutiveTripleEmbedding, firstThreeEmbedding]
        omega
      · refine ⟨1, zero_lt_one, ?_⟩
        simp only [one_smul, simplifiedMatrix_col]
        apply congrArg A.col
        apply Fin.ext
        simp [consecutiveTripleEmbedding, firstThreeEmbedding]
        omega
  have hRightPos : 0 < rightLoops ∨ 1 < terminalSize →
      0 < orderedMinor (simplifiedMatrix A) (allRows 3) (lastThreeEmbedding hm) := by
    have transferTerminal (p : ℕ) (hp : 2 ≤ p) (hpBound : p < n)
        (hpEq : rLast.val = p)
        (hrawPos : 0 < orderedMinor A (allRows 3)
          (terminalTripleEmbedding p hp hpBound)) :
        0 < orderedMinor (simplifiedMatrix A) (allRows 3) (lastThreeEmbedding hm) := by
      apply orderedMinor_simplified_pos_of_positiveScalings
        (A := A) (terminalTripleEmbedding p hp hpBound) (lastThreeEmbedding hm) _ hrawPos
      intro u
      fin_cases u
      · rcases lastThree_firstColumn_positiveScaling hTN hm with ⟨c, hc, hscale⟩
        refine ⟨c, hc, ?_⟩
        simp only [simplifiedMatrix_col]
        change A.col ((terminalTripleEmbedding p hp hpBound) 0) = c •
          A.col (simplificationEmbedding A ⟨simplificationSize A - 3, by omega⟩)
        have hidx : (terminalTripleEmbedding p hp hpBound) 0 =
            (⟨rLast.val - 2, by omega⟩ : Fin n) := by
          apply Fin.ext
          simp [terminalTripleEmbedding]
          omega
        rw [hidx]
        exact hscale
      · refine ⟨1, zero_lt_one, ?_⟩
        simp only [one_smul, simplifiedMatrix_col]
        apply congrArg A.col
        apply Fin.ext
        simp [terminalTripleEmbedding, lastThreeEmbedding]
        omega
      · refine ⟨1, zero_lt_one, ?_⟩
        simp only [one_smul, simplifiedMatrix_col]
        apply congrArg A.col
        apply Fin.ext
        simp [terminalTripleEmbedding, lastThreeEmbedding]
        omega
    intro hprotect
    by_cases hright : 0 < rightLoops
    · have hterm : terminalSize = 1 := hTerminalSingleton hright
      have hrLastzEq : rLast = z := by
        apply Fin.ext
        dsimp [terminalSize] at hterm
        omega
      have hpSucc : z.val + 1 < n := by
        dsimp [rightLoops] at hright
        omega
      have hloops : ∀ j : Fin n, z.val < j.val → IsLoop A j := by
        intro j hj
        exact isLoop_of_lastNonloopIndex_lt hfull (Fin.mk_lt_mk.mpr hj)
      obtain ⟨hp, hrawPos, _⟩ := rankThreeToeplitz_terminalLoops_endpointProtection
        z.isLt hpSucc hTN hfull (by simpa [A] using hloops)
        (by simpa [A, z] using lastNonloopIndex_nonloop A hfull)
      exact transferTerminal z.val hp z.isLt (by simp [hrLastzEq]) hrawPos
    · have hlarge : 2 ≤ terminalSize := by
        rcases hprotect with h | h
        · exact (hright h).elim
        · omega
      have hblock := terminalClass_isMaximalParallelBlock hTN hfull hm (by
        simpa [A, rLast, z, terminalSize] using hlarge)
      have hterminal : rLast.val + terminalSize = n := by
        rcases rankThreeToeplitz_endpointParallel hTN hblock with hp | hterminal
        · have hr0Last : r0 < rLast := (simplificationEmbedding A).strictMono (by
            apply Fin.mk_lt_mk.mpr
            change 0 < m - 1
            omega)
          have : rLast.val = 0 := by simpa [A, rLast] using hp
          omega
        · simpa [A, rLast, z, terminalSize] using hterminal
      obtain ⟨hp, hpBound, hrawPos⟩ :=
        rankThreeToeplitz_terminalParallelBlock_endpointProtection hTN hfull hblock (by
          simpa [A, rLast, z, terminalSize] using hterminal)
      exact transferTerminal rLast.val hp hpBound rfl hrawPos
  refine
    { leftLoopCount := leftLoops
      rightLoopCount := rightLoops
      initialParallelSize := initialSize
      terminalParallelSize := terminalSize
      simplifiedSize := m
      initialParallelSize_pos := hInitialPos
      terminalParallelSize_pos := hTerminalPos
      simplifiedSize_ge_three := hm
      groundSize_eq := hGround
      initialParallel_singleton_of_leftLoops := hInitialSingleton
      terminalParallel_singleton_of_rightLoops := hTerminalSingleton
      intervals := canonicalCollinearIntervals A
      interval_large := ?_
      intervals_separated := ?_
      initial_endpoint_protected := ?_
      terminal_endpoint_protected := ?_
      interval_not_whole := ?_ }
  · intro H hH
    exact canonicalCollinearInterval_large hH
  · intro H hH K hK hHK
    exact canonicalCollinearIntervals_separated hH hK hHK
  · intro hprotect H hH
    exact canonicalCollinearInterval_left_protected hTwo hSlopes hm (hLeftPos hprotect) hH
  · intro hprotect H hH
    exact canonicalCollinearInterval_right_protected hTwo hSlopes hm (hRightPos hprotect) hH
  · intro H hH
    exact canonicalCollinearInterval_not_whole hTwo hfull hSlopes hH

@[simp]
theorem canonicalCompatibleRankThreeData_leftLoopCount
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).leftLoopCount =
      (simplificationEmbedding (rankThreeToeplitz a) ⟨0, by
        have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
        omega⟩).val :=
  rfl

@[simp]
theorem canonicalCompatibleRankThreeData_simplifiedSize
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).simplifiedSize =
      simplificationSize (rankThreeToeplitz a) :=
  rfl

@[simp]
theorem canonicalCompatibleRankThreeData_initialParallelSize
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).initialParallelSize =
      (simplificationEmbedding (rankThreeToeplitz a) ⟨1, by
        have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
        omega⟩).val -
      (simplificationEmbedding (rankThreeToeplitz a) ⟨0, by
        have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
        omega⟩).val :=
  rfl

@[simp]
theorem canonicalCompatibleRankThreeData_rightLoopCount
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).rightLoopCount =
      n - ((lastNonloopIndex (rankThreeToeplitz a) hfull).val + 1) :=
  rfl

@[simp]
theorem canonicalCompatibleRankThreeData_terminalParallelSize
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).terminalParallelSize =
      (lastNonloopIndex (rankThreeToeplitz a) hfull).val + 1 -
      (simplificationEmbedding (rankThreeToeplitz a)
        ⟨simplificationSize (rankThreeToeplitz a) - 1, by
          have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
          omega⟩).val :=
  rfl

@[simp]
theorem canonicalCompatibleRankThreeData_intervals
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).intervals =
      canonicalCollinearIntervals (rankThreeToeplitz a) :=
  rfl

/-- The first index of the canonical terminal loop block is one past the final matrix nonloop. -/
theorem canonicalCompatibleRankThreeData_rightLoopStart
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).rightLoopStart =
      (lastNonloopIndex (rankThreeToeplitz a) hfull).val + 1 := by
  let A := rankThreeToeplitz a
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  change 3 ≤ simplificationSize A at hm
  change 3 ≤ simplificationSize A at hm
  have hlast := internal_simplificationEmbedding_val hTN hm
    (k := simplificationSize A - 1)
    (show 1 ≤ simplificationSize A - 1 by omega)
    (show simplificationSize A - 1 < simplificationSize (rankThreeToeplitz a) by
      change simplificationSize A - 1 < simplificationSize A
      omega)
  simp only [CompatibleRankThreeData.rightLoopStart, CompatibleRankThreeData.terminalStart,
    CompatibleRankThreeData.middleStart, canonicalCompatibleRankThreeData_leftLoopCount,
    canonicalCompatibleRankThreeData_initialParallelSize,
    canonicalCompatibleRankThreeData_simplifiedSize,
    canonicalCompatibleRankThreeData_terminalParallelSize]
  change
    (simplificationEmbedding A ⟨0, by omega⟩).val +
          ((simplificationEmbedding A ⟨1, by omega⟩).val -
            (simplificationEmbedding A ⟨0, by omega⟩).val) +
        (simplificationSize A - 2) +
      ((lastNonloopIndex A hfull).val + 1 -
        (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val) =
      (lastNonloopIndex A hfull).val + 1
  have h01 := (simplificationEmbedding A).strictMono
    (Fin.mk_lt_mk.mpr (by norm_num) :
      (⟨0, by omega⟩ : Fin (simplificationSize A)) < ⟨1, by omega⟩)
  have hLastNonloop := nonloop_le_lastNonloopIndex hfull
    (simplificationEmbedding_not_isLoop A
      (⟨simplificationSize A - 1, by omega⟩ : Fin (simplificationSize A)))
  have hlast' :
      (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val =
        (simplificationEmbedding A ⟨1, by omega⟩).val +
          (simplificationSize A - 2) := by
    simpa [A] using hlast
  have h01sum :
      (simplificationEmbedding A ⟨0, by omega⟩).val +
          ((simplificationEmbedding A ⟨1, by omega⟩).val -
            (simplificationEmbedding A ⟨0, by omega⟩).val) =
        (simplificationEmbedding A ⟨1, by omega⟩).val :=
    Nat.add_sub_of_le h01.le
  have hLastLe :
      (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val ≤
        (lastNonloopIndex A hfull).val + 1 := by
    have hval :
        (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val ≤
          (lastNonloopIndex A hfull).val := hLastNonloop
    exact hval.trans (Nat.le_succ _)
  have hLastSum :
      (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val +
          ((lastNonloopIndex A hfull).val + 1 -
            (simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩).val) =
        (lastNonloopIndex A hfull).val + 1 :=
    Nat.add_sub_of_le hLastLe
  omega

@[simp]
theorem canonicalCompatibleRankThreeData_middleStart
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).middleStart =
      (simplificationEmbedding (rankThreeToeplitz a) ⟨1, by
        have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
        omega⟩).val := by
  rw [CompatibleRankThreeData.middleStart,
    canonicalCompatibleRankThreeData_leftLoopCount,
    canonicalCompatibleRankThreeData_initialParallelSize]
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  have hle := (simplificationEmbedding (rankThreeToeplitz a)).strictMono
    (Fin.mk_lt_mk.mpr (by norm_num) :
      (⟨0, by omega⟩ : Fin (simplificationSize (rankThreeToeplitz a))) < ⟨1, by omega⟩)
  omega

@[simp]
theorem canonicalCompatibleRankThreeData_terminalStart
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) :
    (canonicalCompatibleRankThreeData hTN hfull).terminalStart =
      (simplificationEmbedding (rankThreeToeplitz a)
        ⟨simplificationSize (rankThreeToeplitz a) - 1, by
          have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
          omega⟩).val := by
  rw [CompatibleRankThreeData.terminalStart,
    canonicalCompatibleRankThreeData_middleStart,
    canonicalCompatibleRankThreeData_simplifiedSize]
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  have h := internal_simplificationEmbedding_val hTN hm
    (k := simplificationSize (rankThreeToeplitz a) - 1) (by omega) (by omega)
  simpa using h.symm

/-- The loop blocks of the canonical data agree exactly with the zero columns of the matrix. -/
theorem canonicalCompatibleRankThreeData_isLoop_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) (j : Fin n) :
    (canonicalCompatibleRankThreeData hTN hfull).IsLoop j ↔
      IsLoop (rankThreeToeplitz a) j := by
  let A := rankThreeToeplitz a
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  change 3 ≤ simplificationSize A at hm
  let first : Fin n := simplificationEmbedding A ⟨0, by omega⟩
  let last := lastNonloopIndex A hfull
  rw [CompatibleRankThreeData.IsLoop, CompatibleRankThreeData.IsLeftLoop,
    CompatibleRankThreeData.IsRightLoop,
    canonicalCompatibleRankThreeData_leftLoopCount,
    canonicalCompatibleRankThreeData_rightLoopStart]
  change j.val < first.val ∨ last.val < j.val ↔ IsLoop A j
  constructor
  · rintro (hj | hj)
    · exact isLoop_of_lt_first_simplificationEmbedding (A := A) (by omega)
        (Fin.mk_lt_mk.mpr hj)
    · exact isLoop_of_lastNonloopIndex_lt hfull (Fin.mk_lt_mk.mpr hj)
  · intro hj
    by_contra h
    push Not at h
    exact (rankThreeToeplitz_nonloop_interval (hTN.tnUpTo 2)
      (Fin.mk_le_mk.mpr h.1) (Fin.mk_le_mk.mpr h.2)
      (simplificationEmbedding_not_isLoop A _) (lastNonloopIndex_nonloop A hfull)) hj

/-- On nonloops, the numeric simplification map of the compatible data is the canonical matrix
class number. -/
theorem canonicalCompatibleRankThreeData_simplifiedIndex_eq
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) {j : Fin n}
    (hj : ¬IsLoop (rankThreeToeplitz a) j) :
    (canonicalCompatibleRankThreeData hTN hfull).simplifiedIndex j =
      simplificationClassIndex (rankThreeToeplitz a) j hj := by
  let A := rankThreeToeplitz a
  let D := canonicalCompatibleRankThreeData hTN hfull
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  change 3 ≤ simplificationSize A at hm
  let first : Fin n := simplificationEmbedding A ⟨0, by omega⟩
  let second : Fin n := simplificationEmbedding A ⟨1, by omega⟩
  let last : Fin n := simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩
  have hLastFormula : last.val = second.val + (simplificationSize A - 2) := by
    have h := internal_simplificationEmbedding_val hTN hm
      (k := simplificationSize A - 1)
      (show 1 ≤ simplificationSize A - 1 by omega)
      (show simplificationSize A - 1 < simplificationSize (rankThreeToeplitz a) by
        change simplificationSize A - 1 < simplificationSize A
        omega)
    simpa [A, second, last] using h
  apply Fin.ext
  simp only [CompatibleRankThreeData.simplifiedIndex,
    CompatibleRankThreeData.simplifiedIndexNat,
    canonicalCompatibleRankThreeData_middleStart,
    canonicalCompatibleRankThreeData_terminalStart,
    canonicalCompatibleRankThreeData_simplifiedSize]
  split <;> rename_i hfirst
  · change j.val < second.val at hfirst
    have hpar := columnsPositivelyParallel_first_of_lt_secondRepresentative
      (A := A) (by omega) hfirst hj
    have hc := (simplificationClassIndex_eq_iff A j hj
      (⟨0, by omega⟩ : Fin (simplificationSize A))).mpr hpar
    simpa using congrArg Fin.val hc.symm
  split <;> rename_i hlast
  · change ¬j.val < second.val at hfirst
    change j.val < last.val at hlast
    have hsecondj : second.val ≤ j.val := Nat.le_of_not_gt hfirst
    let qval := j.val - second.val + 1
    have hq1 : 1 ≤ qval := by dsimp [qval]; omega
    have hqLast : qval < simplificationSize A - 1 := by dsimp [qval]; omega
    have hqm : qval < simplificationSize A := by omega
    let q : Fin (simplificationSize A) := ⟨qval, hqm⟩
    have hemb := internal_simplificationEmbedding_val hTN hm hq1 hqm
    have hembVal : (simplificationEmbedding A q).val = j.val := by
      change (simplificationEmbedding A ⟨qval, hqm⟩).val = j.val
      have hemb' :
          (simplificationEmbedding A ⟨qval, hqm⟩).val = second.val + (qval - 1) := by
        simpa [A, second] using hemb
      rw [hemb']
      dsimp [qval]
      omega
    have hjEq : simplificationEmbedding A q = j := Fin.ext hembVal
    have hc : simplificationClassIndex A j hj = q := by
      apply (simplificationClassIndex_eq_iff A j hj q).mpr
      rw [hjEq]
      exact columnsPositivelyParallel_refl A j
    change qval = (simplificationClassIndex A j hj).val
    rw [hc]
  · change ¬j.val < last.val at hlast
    have hlastj : last ≤ j := Fin.mk_le_mk.mpr (Nat.le_of_not_gt hlast)
    have hpar := columnsPositivelyParallel_last_of_lastRepresentative_le
      (A := A) (hTN.tnUpTo 2) (show 0 < simplificationSize A by omega) hlastj hj
    have hc := (simplificationClassIndex_eq_iff A j hj
      (⟨simplificationSize A - 1, by omega⟩ : Fin (simplificationSize A))).mpr hpar
    simpa using congrArg Fin.val hc.symm

/-- Canonical data nonloops are exactly matrix nonloops. -/
theorem canonicalCompatibleRankThreeData_isNonloop_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) (j : Fin n) :
    (canonicalCompatibleRankThreeData hTN hfull).IsNonloop j ↔
      ¬IsLoop (rankThreeToeplitz a) j := by
  rw [(canonicalCompatibleRankThreeData hTN hfull).isNonloop_iff_not_isLoop,
    canonicalCompatibleRankThreeData_isLoop_iff]

/-- The initial endpoint class of the data is exactly canonical simplification class zero. -/
theorem canonicalCompatibleRankThreeData_isInitialParallel_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) (j : Fin n) :
    (canonicalCompatibleRankThreeData hTN hfull).IsInitialParallel j ↔
      ∃ hj : ¬IsLoop (rankThreeToeplitz a) j,
        simplificationClassIndex (rankThreeToeplitz a) j hj =
          ⟨0, by
            have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
            omega⟩ := by
  let A := rankThreeToeplitz a
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  change 3 ≤ simplificationSize A at hm
  let first : Fin n := simplificationEmbedding A ⟨0, by omega⟩
  let second : Fin n := simplificationEmbedding A ⟨1, by omega⟩
  rw [CompatibleRankThreeData.IsInitialParallel,
    canonicalCompatibleRankThreeData_leftLoopCount,
    canonicalCompatibleRankThreeData_middleStart]
  change first.val ≤ j.val ∧ j.val < second.val ↔ _
  constructor
  · intro h
    have hj := rankThreeToeplitz_nonloop_interval (i := first) (j := j) (k := second)
      (hTN.tnUpTo 2)
      (Fin.mk_le_mk.mpr h.1) (Fin.mk_lt_mk.mpr h.2).le
      (simplificationEmbedding_not_isLoop A _) (simplificationEmbedding_not_isLoop A _)
    refine ⟨hj, ?_⟩
    apply (simplificationClassIndex_eq_iff A j hj _).mpr
    exact columnsPositivelyParallel_first_of_lt_secondRepresentative (A := A) (by omega)
      (Fin.mk_lt_mk.mpr h.2) hj
  · rintro ⟨hj, hclass⟩
    have hpar := simplificationClassIndex_parallel A j hj
    rw [hclass] at hpar
    have hrepLe : first ≤ j := by
      have hfirstRep : parallelRepresentative A j = first := by
        rw [← simplificationEmbedding_classIndex_eq_parallelRepresentative A j hj, hclass]
      rw [← hfirstRep]
      exact parallelRepresentative_le (columnsPositivelyParallel_refl A j)
    have hjsecond : j < second := by
      by_contra h
      have hsecondj : second ≤ j := le_of_not_gt h
      have hmono := simplificationClassIndex_mono_of_tnUpTo_two (hTN.tnUpTo 2) hsecondj
        (simplificationEmbedding_not_isLoop A _) hj
      have hsecondClass : simplificationClassIndex A second
          (simplificationEmbedding_not_isLoop A _) = ⟨1, by omega⟩ := by
        apply (simplificationClassIndex_eq_iff A _ _ _).mpr
        exact columnsPositivelyParallel_refl A _
      rw [hsecondClass, hclass] at hmono
      norm_num at hmono
    exact ⟨hrepLe, hjsecond⟩

/-- The terminal endpoint class of the data is exactly the last simplification class. -/
theorem canonicalCompatibleRankThreeData_isTerminalParallel_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a)) (j : Fin n) :
    (canonicalCompatibleRankThreeData hTN hfull).IsTerminalParallel j ↔
      ∃ hj : ¬IsLoop (rankThreeToeplitz a) j,
        simplificationClassIndex (rankThreeToeplitz a) j hj =
          ⟨simplificationSize (rankThreeToeplitz a) - 1, by
            have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
            omega⟩ := by
  let A := rankThreeToeplitz a
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  change 3 ≤ simplificationSize A at hm
  let first : Fin n :=
    simplificationEmbedding A ⟨simplificationSize A - 1, by omega⟩
  let last := lastNonloopIndex A hfull
  rw [CompatibleRankThreeData.IsTerminalParallel,
    canonicalCompatibleRankThreeData_terminalStart,
    canonicalCompatibleRankThreeData_rightLoopStart]
  change first.val ≤ j.val ∧ j.val < last.val + 1 ↔ _
  constructor
  · intro h
    have hj := rankThreeToeplitz_nonloop_interval (i := first) (j := j) (k := last)
      (hTN.tnUpTo 2)
      (Fin.mk_le_mk.mpr h.1) (Fin.mk_le_mk.mpr (Nat.lt_succ_iff.mp h.2))
      (simplificationEmbedding_not_isLoop A _) (lastNonloopIndex_nonloop A hfull)
    refine ⟨hj, ?_⟩
    apply (simplificationClassIndex_eq_iff A j hj _).mpr
    exact columnsPositivelyParallel_last_of_lastRepresentative_le (A := A)
      (hTN.tnUpTo 2) (by omega) (Fin.mk_le_mk.mpr h.1) hj
  · rintro ⟨hj, hclass⟩
    change simplificationClassIndex A j hj =
      (⟨simplificationSize A - 1, by omega⟩ : Fin (simplificationSize A)) at hclass
    have hfirstj : first ≤ j := by
      have hfirstRep : parallelRepresentative A j = first := by
        rw [← simplificationEmbedding_classIndex_eq_parallelRepresentative A j hj, hclass]
      rw [← hfirstRep]
      exact parallelRepresentative_le (columnsPositivelyParallel_refl A j)
    have hjlast := nonloop_le_lastNonloopIndex hfull hj
    exact ⟨hfirstj, Nat.lt_succ_of_le hjlast⟩

/-- A three-element finset is the set of values of its increasing enumeration. -/
theorem finset_eq_three_orderEmb_values {J : Finset (Fin n)} (hJ : J.card = 3) :
    J = {J.orderEmbOfFin hJ 0, J.orderEmbOfFin hJ 1, J.orderEmbOfFin hJ 2} := by
  have hrange := Finset.map_orderEmbOfFin_univ J hJ
  calc
    J = Finset.map (J.orderEmbOfFin hJ).toEmbedding Finset.univ := hrange.symm
    _ = {J.orderEmbOfFin hJ 0, J.orderEmbOfFin hJ 1, J.orderEmbOfFin hJ 2} := by
      ext x
      simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩

/-- The geometric trichotomy for an ordered maximal minor: loops, repeated projective classes,
or containment of three distinct classes in a maximal collinear interval. -/
theorem orderedMinor_eq_zero_iff_canonicalDegeneracy
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (cols : Fin 3 ↪o Fin n) :
    orderedMinor (rankThreeToeplitz a) (allRows 3) cols = 0 ↔
      IsLoop (rankThreeToeplitz a) (cols 0) ∨
      IsLoop (rankThreeToeplitz a) (cols 1) ∨
      IsLoop (rankThreeToeplitz a) (cols 2) ∨
      ColumnsPositivelyParallel (rankThreeToeplitz a) (cols 0) (cols 1) ∨
      ColumnsPositivelyParallel (rankThreeToeplitz a) (cols 1) (cols 2) ∨
      ∃ (h0 : ¬IsLoop (rankThreeToeplitz a) (cols 0))
        (h1 : ¬IsLoop (rankThreeToeplitz a) (cols 1))
        (h2 : ¬IsLoop (rankThreeToeplitz a) (cols 2)),
        simplificationClassIndex (rankThreeToeplitz a) (cols 0) h0 ≠
          simplificationClassIndex (rankThreeToeplitz a) (cols 1) h1 ∧
        simplificationClassIndex (rankThreeToeplitz a) (cols 1) h1 ≠
          simplificationClassIndex (rankThreeToeplitz a) (cols 2) h2 ∧
        ∃ I : MaximalConstantSlopeInterval (rankThreeToeplitz a),
          (simplificationClassIndex (rankThreeToeplitz a) (cols 0) h0).val ∈ I.vertices ∧
          (simplificationClassIndex (rankThreeToeplitz a) (cols 1) h1).val ∈ I.vertices ∧
          (simplificationClassIndex (rankThreeToeplitz a) (cols 2) h2).val ∈ I.vertices := by
  let A := rankThreeToeplitz a
  have hTwo : TNUpTo A 2 := hTN.tnUpTo 2
  have hSlopes : SimplifiedSlopesMonotone A :=
    (totallyNonnegative_iff_tnUpTo_two_and_simplifiedSlopesMonotone A).mp hTN |>.2
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  constructor
  · intro hzero
    by_cases h0 : IsLoop A (cols 0)
    · exact Or.inl h0
    by_cases h1 : IsLoop A (cols 1)
    · exact Or.inr (Or.inl h1)
    by_cases h2 : IsLoop A (cols 2)
    · exact Or.inr (Or.inr (Or.inl h2))
    let p := simplificationClassIndex A (cols 0) h0
    let q := simplificationClassIndex A (cols 1) h1
    let r := simplificationClassIndex A (cols 2) h2
    by_cases hpq : p = q
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ((simplificationClassIndex_eq_iff_columnsPositivelyParallel A h0 h1).mp hpq))))
    by_cases hqr : q = r
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ((simplificationClassIndex_eq_iff_columnsPositivelyParallel A h1 h2).mp hqr)))))
    have hselected := selectedTripleEmbedding_eq cols
    have hzero' := hzero
    rw [← hselected] at hzero'
    have hunique :=
      (orderedMinor_selectedTriple_eq_zero_iff_existsUnique_maximalInterval hTwo hSlopes
        h01 h12 h0 h1 h2 hpq hqr).mp hzero'
    rcases hunique with ⟨I, hI, _⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨h0, h1, h2, hpq, hqr, I, hI⟩))))
  · rintro (h0 | h1 | h2 | h01par | h12par | hcol)
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 0 h0
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 1 h1
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 2 h2
    · exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols (by decide) h01par
    · exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols (by decide) h12par
    · rcases hcol with ⟨h0, h1, h2, hpq, hqr, I, hI⟩
      have hunique : ∃! J : MaximalConstantSlopeInterval A,
          (simplificationClassIndex A (cols 0) h0).val ∈ J.vertices ∧
          (simplificationClassIndex A (cols 1) h1).val ∈ J.vertices ∧
          (simplificationClassIndex A (cols 2) h2).val ∈ J.vertices := by
        refine ⟨I, hI, ?_⟩
        intro J hJ
        exact MaximalConstantSlopeInterval.eq_of_two_common_vertices
          hJ.1 hI.1 hJ.2.2 hI.2.2 (by
            intro heq
            have hle01 := simplificationClassIndex_mono_of_tnUpTo_two hTwo h01.le h0 h1
            have hle12 := simplificationClassIndex_mono_of_tnUpTo_two hTwo h12.le h1 h2
            apply hpq
            apply le_antisymm hle01
            have heqFin : simplificationClassIndex A (cols 0) h0 =
                simplificationClassIndex A (cols 2) h2 := Fin.ext heq
            rw [heqFin]
            exact hle12)
      have hzero :=
        (orderedMinor_selectedTriple_eq_zero_iff_existsUnique_maximalInterval hTwo hSlopes
          h01 h12 h0 h1 h2 hpq hqr).mpr hunique
      rwa [selectedTripleEmbedding_eq cols] at hzero

/-- Two distinct parallel nonloop columns of a totally nonnegative Toeplitz matrix belong to
one of the two endpoint simplification classes. -/
theorem parallel_pair_class_is_endpoint
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    {i j : Fin n} (hij : i < j)
    (hi : ¬IsLoop (rankThreeToeplitz a) i) (hj : ¬IsLoop (rankThreeToeplitz a) j)
    (hpar : ColumnsPositivelyParallel (rankThreeToeplitz a) i j) :
    simplificationClassIndex (rankThreeToeplitz a) i hi =
        ⟨0, by
          have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
          omega⟩ ∨
      simplificationClassIndex (rankThreeToeplitz a) i hi =
        ⟨simplificationSize (rankThreeToeplitz a) - 1, by
          have := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
          omega⟩ := by
  let A := rankThreeToeplitz a
  have hm := three_le_simplificationSize_of_hasFullRowRank (hTN.tnUpTo 2) hfull
  let p := simplificationClassIndex A i hi
  have hpj : simplificationClassIndex A j hj = p := by
    exact (simplificationClassIndex_eq_iff_columnsPositivelyParallel A hi hj).mpr
      hpar |>.symm
  by_cases hp0 : p = ⟨0, by omega⟩
  · exact Or.inl hp0
  by_cases hpLast : p = ⟨simplificationSize A - 1, by omega⟩
  · exact Or.inr hpLast
  have hpPos : 0 < p.val := by
    have := p.isLt
    by_contra h
    have : p.val = 0 := by omega
    exact hp0 (Fin.ext this)
  have hpNext : p.val + 1 < simplificationSize A := by
    have hpBound := p.isLt
    by_contra h
    have hpval : p.val = simplificationSize A - 1 := by omega
    exact hpLast (Fin.ext hpval)
  let pnext : Fin (simplificationSize A) := ⟨p.val + 1, hpNext⟩
  have hrepStep := rankThreeToeplitz_internal_representatives_consecutive hTN hpPos hpNext
  have hrepI := simplificationEmbedding_classIndex_eq_parallelRepresentative A i hi
  have hrepJ := simplificationEmbedding_classIndex_eq_parallelRepresentative A j hj
  have hrepLeI : simplificationEmbedding A p ≤ i := by
    rw [hrepI]
    exact parallelRepresentative_le (columnsPositivelyParallel_refl A i)
  have hjNext : j < simplificationEmbedding A pnext := by
    by_contra h
    have hnextj : simplificationEmbedding A pnext ≤ j := le_of_not_gt h
    have hmono := simplificationClassIndex_mono_of_tnUpTo_two (hTN.tnUpTo 2) hnextj
      (simplificationEmbedding_not_isLoop A _) hj
    have hnextClass : simplificationClassIndex A (simplificationEmbedding A pnext)
        (simplificationEmbedding_not_isLoop A _) = pnext := by
      apply (simplificationClassIndex_eq_iff A _ _ _).mpr
      exact columnsPositivelyParallel_refl A _
    rw [hnextClass, hpj] at hmono
    have hpnext : p < pnext := by
      apply Fin.mk_lt_mk.mpr
      change p.val < p.val + 1
      exact Nat.lt_succ_self _
    exact (not_le_of_gt hpnext) hmono
  have hvals : (simplificationEmbedding A pnext).val = (simplificationEmbedding A p).val + 1 := by
    simpa [A, pnext] using hrepStep
  have hrepVal : (simplificationEmbedding A p).val ≤ i.val := hrepLeI
  have hijVal : i.val < j.val := hij
  have hjraw : j.val < (simplificationEmbedding A pnext).val := hjNext
  omega

/-- On a loop-free displayed triple, the data's simplified image is the set of the three
canonical class numbers. -/
theorem canonicalData_simplifiedImages_triple
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    {i j k : Fin n}
    (hi : ¬IsLoop (rankThreeToeplitz a) i)
    (hj : ¬IsLoop (rankThreeToeplitz a) j)
    (hk : ¬IsLoop (rankThreeToeplitz a) k) :
    (canonicalCompatibleRankThreeData hTN hfull).simplifiedImages {i, j, k} =
      {simplificationClassIndex (rankThreeToeplitz a) i hi,
        simplificationClassIndex (rankThreeToeplitz a) j hj,
        simplificationClassIndex (rankThreeToeplitz a) k hk} := by
  classical
  let D := canonicalCompatibleRankThreeData hTN hfull
  have hiD : D.IsNonloop i :=
    (canonicalCompatibleRankThreeData_isNonloop_iff hTN hfull i).mpr hi
  have hjD : D.IsNonloop j :=
    (canonicalCompatibleRankThreeData_isNonloop_iff hTN hfull j).mpr hj
  have hkD : D.IsNonloop k :=
    (canonicalCompatibleRankThreeData_isNonloop_iff hTN hfull k).mpr hk
  change (canonicalCompatibleRankThreeData hTN hfull).IsNonloop i at hiD
  change (canonicalCompatibleRankThreeData hTN hfull).IsNonloop j at hjD
  change (canonicalCompatibleRankThreeData hTN hfull).IsNonloop k at hkD
  have hiEq := canonicalCompatibleRankThreeData_simplifiedIndex_eq hTN hfull hi
  have hjEq := canonicalCompatibleRankThreeData_simplifiedIndex_eq hTN hfull hj
  have hkEq := canonicalCompatibleRankThreeData_simplifiedIndex_eq hTN hfull hk
  calc
    (canonicalCompatibleRankThreeData hTN hfull).simplifiedImages {i, j, k} =
        {simplificationClassIndex (rankThreeToeplitz a) j hj,
          simplificationClassIndex (rankThreeToeplitz a) i hi,
          simplificationClassIndex (rankThreeToeplitz a) k hk} := by
      ext x
      simp [CompatibleRankThreeData.simplifiedImages,
        CompatibleRankThreeData.simplifiedIndex?, hiD, hjD, hkD, hiEq, hjEq, hkEq]
      rfl
    _ = _ := by
      exact Finset.insert_comm _ _ _

/-- The canonical data's triple-nonbasis predicate agrees exactly with vanishing of the
corresponding ordered maximal minor. -/
theorem canonicalCompatibleRankThreeData_tripleNonbasis_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (J : Finset (Fin n)) (hJ : J.card = 3) :
    (canonicalCompatibleRankThreeData hTN hfull).TripleNonbasis J ↔
      orderedMinor (rankThreeToeplitz a) (allRows 3) (J.orderEmbOfFin hJ) = 0 := by
  classical
  let A := rankThreeToeplitz a
  let D := canonicalCompatibleRankThreeData hTN hfull
  let cols := J.orderEmbOfFin hJ
  let i := cols 0
  let j := cols 1
  let k := cols 2
  have h01 : i < j := cols.strictMono (by decide)
  have h12 : j < k := cols.strictMono (by decide)
  have hiJ : i ∈ J := J.orderEmbOfFin_mem hJ 0
  have hjJ : j ∈ J := J.orderEmbOfFin_mem hJ 1
  have hkJ : k ∈ J := J.orderEmbOfFin_mem hJ 2
  have hJijk : J = {i, j, k} := by
    simpa [i, j, k, cols] using finset_eq_three_orderEmb_values hJ
  constructor
  · intro hD
    by_cases hi : IsLoop A i
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 0 hi
    by_cases hj : IsLoop A j
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 1 hj
    by_cases hk : IsLoop A k
    · exact orderedMinor_allRows_eq_zero_of_isLoop A cols 2 hk
    rcases hD.2 with hloops | hinitial | hterminal | hcollinear
    · rcases hloops with ⟨e, heJ, heLoop⟩
      have heLoop' : IsLoop A e :=
        (canonicalCompatibleRankThreeData_isLoop_iff hTN hfull e).mp heLoop
      rw [hJijk] at heJ
      simp only [Finset.mem_insert, Finset.mem_singleton] at heJ
      rcases heJ with rfl | rfl | rfl
      · exact (hi heLoop').elim
      · exact (hj heLoop').elim
      · exact (hk heLoop').elim
    · have hcard : 1 < (J.filter D.IsInitialParallel).card :=
        lt_of_lt_of_le (by norm_num) hinitial
      rcases Finset.one_lt_card.mp hcard with ⟨e, he, f, hf, hef⟩
      have heD := (Finset.mem_filter.mp he).2
      have hfD := (Finset.mem_filter.mp hf).2
      rcases (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull e).mp heD with
        ⟨heNonloop, heClass⟩
      rcases (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull f).mp hfD with
        ⟨hfNonloop, hfClass⟩
      have hefPar : ColumnsPositivelyParallel A e f :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel A heNonloop hfNonloop).mp
          (heClass.trans hfClass.symm)
      have heRange : e ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp he).1
      have hfRange : f ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp hf).1
      rw [← Finset.range_orderEmbOfFin J hJ] at heRange hfRange
      rcases heRange with ⟨re, rfl⟩
      rcases hfRange with ⟨rf, rfl⟩
      have hrfNe : re ≠ rf := fun h ↦ hef (congrArg cols h)
      exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols hrfNe hefPar
    · have hcard : 1 < (J.filter D.IsTerminalParallel).card :=
        lt_of_lt_of_le (by norm_num) hterminal
      rcases Finset.one_lt_card.mp hcard with ⟨e, he, f, hf, hef⟩
      have heD := (Finset.mem_filter.mp he).2
      have hfD := (Finset.mem_filter.mp hf).2
      rcases (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull e).mp heD with
        ⟨heNonloop, heClass⟩
      rcases (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull f).mp hfD with
        ⟨hfNonloop, hfClass⟩
      have hefPar : ColumnsPositivelyParallel A e f :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel A heNonloop hfNonloop).mp
          (heClass.trans hfClass.symm)
      have heRange : e ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp he).1
      have hfRange : f ∈ (J : Set (Fin n)) := (Finset.mem_filter.mp hf).1
      rw [← Finset.range_orderEmbOfFin J hJ] at heRange hfRange
      rcases heRange with ⟨re, rfl⟩
      rcases hfRange with ⟨rf, rfl⟩
      have hrfNe : re ≠ rf := fun h ↦ hef (congrArg cols h)
      exact orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols hrfNe hefPar
    · rcases hcollinear with ⟨himagesCard, H, hHD, himagesH⟩
      rw [hJijk] at himagesCard himagesH
      have himages := canonicalData_simplifiedImages_triple hTN hfull hi hj hk
      rw [himages] at himagesCard
      change ({simplificationClassIndex A i hi, simplificationClassIndex A j hj,
        simplificationClassIndex A k hk} : Finset (Fin (simplificationSize A))).card = 3
        at himagesCard
      have hpq : simplificationClassIndex A i hi ≠ simplificationClassIndex A j hj := by
        intro hpq
        rw [hpq] at himagesCard
        have hdup : ({simplificationClassIndex A j hj, simplificationClassIndex A j hj,
            simplificationClassIndex A k hk} : Finset (Fin (simplificationSize A))) =
            {simplificationClassIndex A j hj, simplificationClassIndex A k hk} := by
          ext x
          simp
        rw [hdup] at himagesCard
        have htwo : ({simplificationClassIndex A j hj,
            simplificationClassIndex A k hk} : Finset (Fin (simplificationSize A))).card ≤ 2 :=
          Finset.card_le_two
        omega
      have hqr : simplificationClassIndex A j hj ≠ simplificationClassIndex A k hk := by
        intro hqr
        rw [hqr] at himagesCard
        have hdup : ({simplificationClassIndex A i hi, simplificationClassIndex A k hk,
            simplificationClassIndex A k hk} : Finset (Fin (simplificationSize A))) =
            {simplificationClassIndex A i hi, simplificationClassIndex A k hk} := by
          ext x
          simp
        rw [hdup] at himagesCard
        have htwo : ({simplificationClassIndex A i hi,
            simplificationClassIndex A k hk} : Finset (Fin (simplificationSize A))).card ≤ 2 :=
          Finset.card_le_two
        omega
      rw [canonicalCompatibleRankThreeData_intervals] at hHD
      rcases mem_canonicalCollinearIntervals.mp hHD with ⟨I, hIl, hIr⟩
      have hpi : (simplificationClassIndex A i hi).val ∈ I.vertices := by
        rw [MaximalConstantSlopeInterval.mem_vertices]
        have hiPoint : simplificationClassIndex A i hi ∈ H.points := by
          apply himagesH
          rw [himages]
          exact Finset.mem_insert_self _ _
        have hiBounds : H.left ≤ simplificationClassIndex A i hi ∧
            simplificationClassIndex A i hi ≤ H.right :=
          SimplifiedInterval.mem_points.mp hiPoint
        exact ⟨by rw [hIl]; exact hiBounds.1, by rw [hIr]; exact hiBounds.2⟩
      have hpj : (simplificationClassIndex A j hj).val ∈ I.vertices := by
        rw [MaximalConstantSlopeInterval.mem_vertices]
        have hjPoint : simplificationClassIndex A j hj ∈ H.points := by
          apply himagesH
          rw [himages]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
        have hjBounds : H.left ≤ simplificationClassIndex A j hj ∧
            simplificationClassIndex A j hj ≤ H.right :=
          SimplifiedInterval.mem_points.mp hjPoint
        exact ⟨by rw [hIl]; exact hjBounds.1, by rw [hIr]; exact hjBounds.2⟩
      have hpk : (simplificationClassIndex A k hk).val ∈ I.vertices := by
        rw [MaximalConstantSlopeInterval.mem_vertices]
        have hkPoint : simplificationClassIndex A k hk ∈ H.points := by
          apply himagesH
          rw [himages]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        have hkBounds : H.left ≤ simplificationClassIndex A k hk ∧
            simplificationClassIndex A k hk ≤ H.right :=
          SimplifiedInterval.mem_points.mp hkPoint
        exact ⟨by rw [hIl]; exact hkBounds.1, by rw [hIr]; exact hkBounds.2⟩
      apply (orderedMinor_eq_zero_iff_canonicalDegeneracy hTN cols).mpr
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hi, hj, hk, hpq, hqr, I, hpi, hpj, hpk⟩))))
  · intro hzero
    refine ⟨hJ, ?_⟩
    by_cases hi : IsLoop A i
    · exact Or.inl ⟨i, hiJ, (canonicalCompatibleRankThreeData_isLoop_iff hTN hfull i).mpr hi⟩
    by_cases hj : IsLoop A j
    · exact Or.inl ⟨j, hjJ, (canonicalCompatibleRankThreeData_isLoop_iff hTN hfull j).mpr hj⟩
    by_cases hk : IsLoop A k
    · exact Or.inl ⟨k, hkJ, (canonicalCompatibleRankThreeData_isLoop_iff hTN hfull k).mpr hk⟩
    rcases (orderedMinor_eq_zero_iff_canonicalDegeneracy hTN cols).mp hzero with
      hi' | hj' | hk' | hijPar | hjkPar | hcol
    · exact (hi hi').elim
    · exact (hj hj').elim
    · exact (hk hk').elim
    · rcases parallel_pair_class_is_endpoint hTN hfull h01 hi hj hijPar with hfirst | hlast
      · apply Or.inr (Or.inl ?_)
        unfold CompatibleRankThreeData.ContainsInitialParallelPair
        have hiD :=
          (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull i).mpr ⟨hi, hfirst⟩
        have hjClass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel A hi hj).mpr hijPar
        have hjD := (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull j).mpr
          ⟨hj, hjClass.symm.trans hfirst⟩
        have hsub : ({i, j} : Finset (Fin n)) ⊆ J.filter D.IsInitialParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hiJ, hiD⟩
          · exact Finset.mem_filter.mpr ⟨hjJ, hjD⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h01] using hcard
      · apply Or.inr (Or.inr (Or.inl ?_))
        unfold CompatibleRankThreeData.ContainsTerminalParallelPair
        have hiD :=
          (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull i).mpr ⟨hi, hlast⟩
        have hjClass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel A hi hj).mpr hijPar
        have hjD := (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull j).mpr
          ⟨hj, hjClass.symm.trans hlast⟩
        have hsub : ({i, j} : Finset (Fin n)) ⊆ J.filter D.IsTerminalParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hiJ, hiD⟩
          · exact Finset.mem_filter.mpr ⟨hjJ, hjD⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h01] using hcard
    · rcases parallel_pair_class_is_endpoint hTN hfull h12 hj hk hjkPar with hfirst | hlast
      · apply Or.inr (Or.inl ?_)
        unfold CompatibleRankThreeData.ContainsInitialParallelPair
        have hjD :=
          (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull j).mpr ⟨hj, hfirst⟩
        have hkClass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel A hj hk).mpr hjkPar
        have hkD := (canonicalCompatibleRankThreeData_isInitialParallel_iff hTN hfull k).mpr
          ⟨hk, hkClass.symm.trans hfirst⟩
        have hsub : ({j, k} : Finset (Fin n)) ⊆ J.filter D.IsInitialParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hjJ, hjD⟩
          · exact Finset.mem_filter.mpr ⟨hkJ, hkD⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h12] using hcard
      · apply Or.inr (Or.inr (Or.inl ?_))
        unfold CompatibleRankThreeData.ContainsTerminalParallelPair
        have hjD :=
          (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull j).mpr ⟨hj, hlast⟩
        have hkClass :=
          (simplificationClassIndex_eq_iff_columnsPositivelyParallel A hj hk).mpr hjkPar
        have hkD := (canonicalCompatibleRankThreeData_isTerminalParallel_iff hTN hfull k).mpr
          ⟨hk, hkClass.symm.trans hlast⟩
        have hsub : ({j, k} : Finset (Fin n)) ⊆ J.filter D.IsTerminalParallel := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨hjJ, hjD⟩
          · exact Finset.mem_filter.mpr ⟨hkJ, hkD⟩
        have hcard := Finset.card_le_card hsub
        simpa [ne_of_lt h12] using hcard
    · rcases hcol with ⟨hi, hj, hk, hpq, hqr, I, hpi, hpj, hpk⟩
      apply Or.inr (Or.inr (Or.inr ?_))
      have himages := canonicalData_simplifiedImages_triple hTN hfull hi hj hk
      constructor
      · rw [hJijk, himages]
        have hik : simplificationClassIndex A (cols 0) hi ≠
            simplificationClassIndex A (cols 2) hk := by
          intro hik
          have hle01 := simplificationClassIndex_mono_of_tnUpTo_two (hTN.tnUpTo 2) h01.le hi hj
          have hle12 := simplificationClassIndex_mono_of_tnUpTo_two (hTN.tnUpTo 2) h12.le hj hk
          apply hpq
          apply le_antisymm hle01
          rw [hik]
          exact hle12
        exact Finset.card_eq_three.mpr ⟨_, _, _, hpq, hik, hqr, rfl⟩
      · let H : SimplifiedInterval (simplificationSize A) :=
          { left := ⟨I.start, lt_of_le_of_lt (by
              have := I.nontrivial
              omega) I.stop_lt⟩
            right := ⟨I.stop, I.stop_lt⟩
            left_le_right := Fin.mk_le_mk.mpr (by have := I.nontrivial; omega) }
        refine ⟨H, ?_, ?_⟩
        · change H ∈ canonicalCollinearIntervals A
          apply mem_canonicalCollinearIntervals.mpr
          exact ⟨I, rfl, rfl⟩
        · rw [hJijk, himages]
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact SimplifiedInterval.mem_points.mpr
              ⟨Fin.mk_le_mk.mpr hpi.1, Fin.mk_le_mk.mpr hpi.2⟩
          · rcases Finset.mem_insert.mp hx with rfl | hx
            · exact SimplifiedInterval.mem_points.mpr
                ⟨Fin.mk_le_mk.mpr hpj.1, Fin.mk_le_mk.mpr hpj.2⟩
            · have hxk := Finset.mem_singleton.mp hx
              subst x
              exact SimplifiedInterval.mem_points.mpr
                ⟨Fin.mk_le_mk.mpr hpk.1, Fin.mk_le_mk.mpr hpk.2⟩

/-- The finite basis support of the canonical data is exactly the nonzero ordered maximal-minor
support of the Toeplitz matrix. -/
theorem mem_canonicalCompatibleRankThreeData_basisFinsets_iff
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    {J : Finset (Fin n)} :
    J ∈ (canonicalCompatibleRankThreeData hTN hfull).basisFinsets ↔
      ∃ hJ : J.card = 3,
        orderedMinor (rankThreeToeplitz a) (allRows 3) (J.orderEmbOfFin hJ) ≠ 0 := by
  rw [CompatibleRankThreeData.mem_basisFinsets_iff]
  constructor
  · rintro ⟨hJ, hnonbasis⟩
    refine ⟨hJ, ?_⟩
    intro hzero
    exact hnonbasis ((canonicalCompatibleRankThreeData_tripleNonbasis_iff hTN hfull J hJ).mpr hzero)
  · rintro ⟨hJ, hnonzero⟩
    refine ⟨hJ, ?_⟩
    intro hnonbasis
    exact hnonzero ((canonicalCompatibleRankThreeData_tripleNonbasis_iff hTN hfull J hJ).mp
      hnonbasis)

/-- Equality of the finite basis systems of compatible data is equivalent to equality of their
triple-nonbasis predicates. -/
theorem sameCompatibleTripleSupport_of_basisFinsets_eq
    (D E : CompatibleRankThreeData n) (hDE : D.basisFinsets = E.basisFinsets) :
    SameCompatibleTripleSupport D E := by
  intro J
  by_cases hJ : J.card = 3
  · have hmem : J ∈ D.basisFinsets ↔ J ∈ E.basisFinsets := by rw [hDE]
    simp only [CompatibleRankThreeData.mem_basisFinsets_iff, hJ, true_and] at hmem
    tauto
  · constructor <;> intro h
    · exact (hJ h.1).elim
    · exact (hJ h.1).elim

/-- Basis support uniquely determines the canonical recovered loop set, endpoint-parallel
relation, and maximal rank-two-flat family. -/
theorem canonicalCompatibleRankThreeData_support_unique
    (hTN : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (E : CompatibleRankThreeData n)
    (hbasis : (canonicalCompatibleRankThreeData hTN hfull).basisFinsets = E.basisFinsets) :
    (canonicalCompatibleRankThreeData hTN hfull).supportLoops = E.supportLoops ∧
      (canonicalCompatibleRankThreeData hTN hfull).supportParallelPairs = E.supportParallelPairs ∧
      (canonicalCompatibleRankThreeData hTN hfull).supportRankTwoFlats = E.supportRankTwoFlats :=
  (canonicalCompatibleRankThreeData hTN hfull).supportComponents_eq_of_sameSupport E
    (sameCompatibleTripleSupport_of_basisFinsets_eq _ _ hbasis)


end

end ToeplitzPositroids
