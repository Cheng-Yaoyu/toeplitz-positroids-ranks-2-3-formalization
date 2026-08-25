import ToeplitzPositroids.Edrei.FiniteFactorNetworkCancellation
import ToeplitzPositroids.Edrei.FiniteFactorNetworkTableau
import ToeplitzPositroids.Edrei.FiniteFactorTN
import ToeplitzPositroids.Edrei.SkewTableauExpansion

/-!
# The unconditional gamma-zero finite-factor bridge

This file specializes the generic finite-network LGV expansion to the reflected endpoints of an
increasing tuple minor.  It identifies the path-sum determinant with the Toeplitz minor and turns
nonemptiness of the disjoint-path family into strict positivity.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- At gamma zero, an arbitrary natural Toeplitz entry is the corresponding finite-factor
coefficient, while a negative entry is zero. -/
theorem FiniteEdreiData.coefficient_eq_finiteFactorCoefficient_of_gamma_eq_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) (i j : ℕ) :
    D.coefficient ((j : ℤ) - (i : ℤ)) =
      if i ≤ j then D.finiteFactorCoefficient (j - i) else 0 := by
  by_cases hij : i ≤ j
  · rw [if_pos hij]
    have hnonneg : (0 : ℤ) ≤ (j : ℤ) - (i : ℤ) := by omega
    rw [FiniteEdreiData.coefficient, if_pos hnonneg]
    have htoNat : ((j : ℤ) - (i : ℤ)).toNat = j - i := by omega
    rw [htoNat, FiniteEdreiData.natCoefficient_eq_finiteFactorCoefficient D hgamma]
    rfl
  · rw [if_neg hij]
    apply D.coefficient_eq_zero_of_neg
    omega

@[simp]
theorem reverseFiniteEdreiData_finiteFactor {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).finiteFactor = D.finiteFactor := by
  simp [FiniteEdreiData.finiteFactor]

@[simp]
theorem reverseFiniteEdreiData_finiteFactorCoefficient
    {p q : ℕ} (D : FiniteEdreiData p q) (n : ℕ) :
    (reverseFiniteEdreiData D).finiteFactorCoefficient n = D.finiteFactorCoefficient n := by
  simp [FiniteEdreiData.finiteFactorCoefficient]

/-- The path-sum matrix for the reflected tuple network. -/
def tupleNetworkPathMatrix
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun a b ↦ FiniteFactorPath.pathSum (reverseFiniteEdreiData D) (tupleNetworkBound J)
    (tupleNetworkSource J a) (tupleNetworkSink I J hstruct b)

/-- A reflected path entry is the correspondingly reversed entry of the tuple minor matrix. -/
theorem tupleNetworkPathMatrix_apply
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (a b : Fin r) :
    tupleNetworkPathMatrix D I J hstruct a b =
      oneSidedToeplitzMinorMatrix D.coefficient I.zeroBasedOrderEmbedding
        J.zeroBasedOrderEmbedding b.rev a.rev := by
  unfold tupleNetworkPathMatrix oneSidedToeplitzMinorMatrix
  simp only [IncreasingIndexTuple.zeroBasedOrderEmbedding_apply]
  by_cases hentry : I b.rev ≤ J a.rev
  · have hsource : (tupleNetworkSource J a).val ≤
        (tupleNetworkSink I J hstruct b).val := by
      simp only [tupleNetworkSource_val, tupleNetworkSink_val]
      have hJbound := J.value_le_tupleWidth a.rev
      have hIbound := (hentry.trans (J.value_le_tupleWidth a.rev))
      have hIpos := I.position_le b.rev
      have hJpos := J.position_le a.rev
      omega
    rw [FiniteFactorPath.pathSum_eq_finiteFactorCoefficient _ hsource,
      reverseFiniteEdreiData_finiteFactorCoefficient]
    rw [FiniteEdreiData.coefficient_eq_finiteFactorCoefficient_of_gamma_eq_zero
      D hgamma (I b.rev - 1) (J a.rev - 1), if_pos]
    · congr 1
      change J.tupleWidth - (I b.rev - 1) -
          (J.tupleWidth - (J a.rev - 1)) =
        (J a.rev - 1) - (I b.rev - 1)
      have hIbound := hentry.trans (J.value_le_tupleWidth a.rev)
      have hJbound := J.value_le_tupleWidth a.rev
      have hIpos := I.position_le b.rev
      have hJpos := J.position_le a.rev
      omega
    · have hIpos := I.position_le b.rev
      have hJpos := J.position_le a.rev
      omega
  · have hsource : ¬(tupleNetworkSource J a).val ≤
        (tupleNetworkSink I J hstruct b).val := by
      simp only [tupleNetworkSource_val, tupleNetworkSink_val]
      have hJbound := J.value_le_tupleWidth a.rev
      have hIpos := I.position_le b.rev
      have hJpos := J.position_le a.rev
      omega
    rw [← FiniteFactorWalk.networkTransfer_apply_eq_pathSum,
      FiniteEdreiData.networkTransfer_apply_eq_finiteFactorCoefficient,
      if_neg hsource]
    rw [FiniteEdreiData.coefficient_eq_finiteFactorCoefficient_of_gamma_eq_zero
      D hgamma (I b.rev - 1) (J a.rev - 1), if_neg]
    have hIpos := I.position_le b.rev
    have hJpos := J.position_le a.rev
    omega

/-- Reversing both row and column orders and transposing does not change the tuple determinant. -/
theorem tupleNetworkPathMatrix_det
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    (tupleNetworkPathMatrix D I J hstruct).det =
      FiniteEdreiData.finiteFactorMinor D I J := by
  let M := oneSidedToeplitzMinorMatrix D.coefficient I.zeroBasedOrderEmbedding
    J.zeroBasedOrderEmbedding
  have hmatrix : tupleNetworkPathMatrix D I J hstruct =
      Matrix.reindex Fin.revPerm Fin.revPerm M.transpose := by
    ext a b
    rw [tupleNetworkPathMatrix_apply D hgamma]
    rfl
  rw [hmatrix, Matrix.det_reindex_self, Matrix.det_transpose]
  rfl

/-- The generic cancellation construction, specialized to a structurally admissible tuple minor. -/
noncomputable def tupleNetworkLGVExpansion
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    LGVExpansion (FiniteEdreiData.finiteFactorMinor D I J) := by
  let E := finiteFactorNetworkLGVExpansion (reverseFiniteEdreiData D)
    (tupleNetworkSource J) (tupleNetworkSink I J hstruct)
  exact
    { term := E.term
      termFintype := E.termFintype
      good := E.good
      goodDecidable := E.goodDecidable
      signedWeight := E.signedWeight
      value_eq_sum := by
        rw [← tupleNetworkPathMatrix_det D hgamma I J hstruct]
        exact E.value_eq_sum
      cancellation := E.cancellation }

/-- Every good reflected term has positive signed weight because its permutation is the identity. -/
theorem tupleNetwork_good_signedWeight_pos
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (T : TupleFiniteFactorNetworkTerm D I J hstruct) (hgood : NetworkTermGood T) :
    0 < networkTermSignedWeight T := by
  unfold networkTermSignedWeight
  have hsign : T.1.sign = 1 := by
    simpa using congrArg Equiv.Perm.sign (tupleNetwork_good_perm_eq_refl T hgood)
  rw [hsign]
  simpa using (Finset.prod_pos fun b (_ : b ∈ Finset.univ) ↦ (T.2 b).weight_pos)

/-- For structurally admissible tuples, the finite-factor minor is positive exactly when the
reflected network has a vertex-disjoint path family. -/
theorem finiteFactorMinor_pos_iff_nonempty_tuple_paths
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      Nonempty (TupleVertexDisjointPathFamily D I J hstruct) := by
  let E := tupleNetworkLGVExpansion D hgamma I J hstruct
  rw [E.eq_sum_good]
  unfold LGVExpansion.goodSum
  letI := E.termFintype
  letI := E.goodDecidable
  constructor
  · intro hpos
    by_contra hempty
    haveI : IsEmpty {T : E.term // E.good T} := not_nonempty_iff.mp hempty
    simp at hpos
  · rintro ⟨T⟩
    apply Finset.sum_pos
    · intro U _
      exact tupleNetwork_good_signedWeight_pos D I J hstruct U.1 U.2
    · exact ⟨T, Finset.mem_univ T⟩

end

end ToeplitzPositroids.Edrei
