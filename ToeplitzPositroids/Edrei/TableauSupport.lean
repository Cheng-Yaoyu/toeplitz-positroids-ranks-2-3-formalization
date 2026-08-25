import ToeplitzPositroids.Edrei.SkewTableauBounds
import ToeplitzPositroids.Edrei.SkewTableauFromTuple

/-!
# Support of the concrete tableau family

The finite skew-tableau family already has the correct hook support.  This file proves that
statement independently of the weighted network identity, which is discharged by
`NetworkTableauWeightBridge`.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

theorem tupleCoproduct_nonempty_iff_hasIntermediateStripPartition
    {p q r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) :
    Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) ↔
      HasIntermediateStripPartition I J p q := by
  constructor
  · rintro ⟨T⟩
    let M := T.intermediate.middle
    let nu : ℕ → ℕ := fun t ↦ if ht : t < r then M ⟨t, ht⟩ else 0
    have hpartition : IsPartitionSequence nu := by
      intro t u htu
      by_cases hu : u < r
      · have ht : t < r := lt_of_le_of_lt htu hu
        simp only [nu, dif_pos ht, dif_pos hu]
        exact M.antitone (by simpa using htu)
      · simp [nu, hu]
    have hinner : ∀ t, I.associatedPartZeroTail t ≤ nu t := by
      intro t
      by_cases ht : t < r
      · rw [IncreasingIndexTuple.associatedPartZeroTail_apply I ht]
        simp only [nu, dif_pos ht]
        exact T.intermediate.inner_le ⟨t, ht⟩
      · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
    have houter : ∀ t, nu t ≤ J.associatedPartZeroTail t := by
      intro t
      by_cases ht : t < r
      · rw [IncreasingIndexTuple.associatedPartZeroTail_apply J ht]
        simp only [nu, dif_pos ht]
        exact T.intermediate.outer_ge ⟨t, ht⟩
      · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
    have hrow : ∀ t, J.associatedPartZeroTail t - nu t ≤ q := by
      intro t
      by_cases ht : t < r
      · rw [IncreasingIndexTuple.associatedPartZeroTail_apply J ht]
        simp only [nu, dif_pos ht]
        have hfit := T.strip_bounds.2
        rw [FiniteSkewShape.fitsRowBound_iff] at hfit
        exact hfit ⟨t, ht⟩
      · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
    have hcolumn : ∀ t, nu (t + p) ≤ I.associatedPartZeroTail t := by
      intro t
      by_cases htp : t + p < r
      · have ht : t < r := by omega
        have hfit := T.strip_bounds.1
        rw [FiniteSkewShape.fitsColumnBound_iff_shift] at hfit
        have h := hfit ⟨t, by omega⟩
        rw [IncreasingIndexTuple.associatedPartZeroTail_apply I ht]
        simp only [nu, dif_pos htp]
        exact h
      · simp [nu, htp]
    exact ⟨nu, hpartition, hinner, houter, hrow, hcolumn⟩
  · intro hstrip
    obtain ⟨nu, hpartition, hinner, houter, hrow, hcolumn⟩ := hstrip
    let middle : RectanglePartition r J.tupleWidth :=
      { rowLength := fun t ↦ ⟨nu t.val, by
          have houter_t := houter t.val
          rw [IncreasingIndexTuple.associatedPartZeroTail_apply J t.isLt] at houter_t
          exact Nat.lt_succ_of_le (houter_t.trans (J.associatedPart_le_tupleWidth t))
        ⟩
        antitone := by
          intro t u htu
          exact hpartition htu }
    let N : IntermediateRectanglePartition
        (containedInnerPartition I J hstruct) (containingOuterPartition J) :=
      { middle := middle
        inner_le := by
          intro t
          change I.associatedPart t ≤ nu t.val
          rw [← IncreasingIndexTuple.associatedPartZeroTail_apply I t.isLt]
          exact hinner t.val
        outer_ge := by
          intro t
          change nu t.val ≤ J.associatedPart t
          rw [← IncreasingIndexTuple.associatedPartZeroTail_apply J t.isLt]
          exact houter t.val }
    apply (SupersymmetricCoproductTableau.nonempty_iff_exists_intermediate).mpr
    refine ⟨N, ?_, ?_⟩
    · rw [FiniteSkewShape.fitsColumnBound_iff_shift]
      intro t
      have htp : t.val + p < r := by omega
      change nu (t.val + p) ≤ I.associatedPart ⟨t.val, by omega⟩
      have hc := hcolumn t.val
      rw [IncreasingIndexTuple.associatedPartZeroTail_apply I (by omega)] at hc
      exact hc
    · rw [FiniteSkewShape.fitsRowBound_iff]
      intro t
      change J.associatedPart t - nu t.val ≤ q
      rw [← IncreasingIndexTuple.associatedPartZeroTail_apply J t.isLt]
      exact hrow t.val

theorem tupleCoproduct_nonempty_iff_indexHook
    {p q r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) :
    Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) ↔
      IndexHookInequalities I J p q := by
  rw [tupleCoproduct_nonempty_iff_hasIntermediateStripPartition I J hstruct,
    hasIntermediateStripPartition_iff_partitionHook I J p q hstruct,
    partitionHookInequalities_iff_indexHook]

theorem tupleCoproductWeight_sum_pos_iff_indexHook
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    0 < ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
      tupleCoproductWeight D I J hstruct T ↔
      IndexHookInequalities I J p q := by
  classical
  constructor
  · intro hpos
    have hnonempty : Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) := by
      by_contra hempty
      letI : IsEmpty (TupleCoproductTableau (p := p) (q := q) I J hstruct) :=
        not_nonempty_iff.mp hempty
      simp at hpos
    exact (tupleCoproduct_nonempty_iff_indexHook I J hstruct).mp hnonempty
  · intro hhook
    have hnonempty := (tupleCoproduct_nonempty_iff_indexHook I J hstruct).mpr hhook
    obtain ⟨T⟩ := hnonempty
    apply Finset.sum_pos
    · intro U _
      exact tupleCoproductWeight_pos D I J hstruct U
    · exact ⟨T, Finset.mem_univ T⟩

end

end ToeplitzPositroids.Edrei
