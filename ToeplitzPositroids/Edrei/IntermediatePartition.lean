import ToeplitzPositroids.Edrei.HookTranslation

/-!
# Intermediate partitions for finite Edrei data

This file combines the zero-tail partition construction with the Toeplitz index
translation.  It formalizes the existence argument around equations
(10.10)--(10.12), independently of symmetric-function evaluations.
-/

namespace ToeplitzPositroids.Edrei

open IncreasingIndexTuple

/-- The infinite zero-tail hook family is equivalent to the finite sharp index
family in the manuscript. -/
theorem zeroTailPartitionHook_iff_indexHook {r p q : ℕ} (hp : p ≤ r)
    (I J : IncreasingIndexTuple r) :
    (∀ t : ℕ,
        J.associatedPartZeroTail (t + p) ≤ I.associatedPartZeroTail t + q) ↔
      ∀ t : Fin (r - p),
        J (shiftedPartitionIndex hp t).rev + p ≤
          I (unshiftedPartitionIndex hp t).rev + q := by
  rw [← partitionHookFamily_iff_indexHookFamily hp I J]
  constructor
  · intro h t
    have ht : t.val < r := by omega
    have htp : t.val + p < r := by omega
    simpa [associatedPartZeroTail_apply I ht,
      associatedPartZeroTail_apply J htp,
      shiftedPartitionIndex, unshiftedPartitionIndex] using h t.val
  · intro h t
    by_cases htp : t + p < r
    · have ht : t < r := by omega
      have hs : t < r - p := by omega
      have hfinite := h ⟨t, hs⟩
      simpa [associatedPartZeroTail_apply I ht,
        associatedPartZeroTail_apply J htp,
        shiftedPartitionIndex, unshiftedPartitionIndex] using hfinite
    · have hz : J.associatedPartZeroTail (t + p) = 0 := by
        simp [associatedPartZeroTail, htp]
      rw [hz]
      exact Nat.zero_le _

/-- An intermediate partition satisfying both strip conditions exists exactly
under the Toeplitz hook inequalities, assuming structural containment. -/
theorem exists_intermediatePartition_iff_indexHook
    {r p q : ℕ} (hp : p ≤ r) (I J : IncreasingIndexTuple r)
    (hstructural : ∀ k, I k ≤ J k) :
    (∃ nu : ℕ → ℕ,
        IsPartitionSequence nu ∧
        (∀ t, I.associatedPartZeroTail t ≤ nu t) ∧
        (∀ t, nu t ≤ J.associatedPartZeroTail t) ∧
        (∀ t, J.associatedPartZeroTail t - nu t ≤ q) ∧
        (∀ t, nu (t + p) ≤ I.associatedPartZeroTail t)) ↔
      ∀ t : Fin (r - p),
        J (shiftedPartitionIndex hp t).rev + p ≤
          I (unshiftedPartitionIndex hp t).rev + q := by
  rw [exists_intermediatePartition_iff_hook
    I.associatedPartZeroTail_isPartitionSequence
    J.associatedPartZeroTail_isPartitionSequence
    ((associatedPartZeroTail_forall_le_iff I J).2 hstructural) p q]
  exact zeroTailPartitionHook_iff_indexHook hp I J

end ToeplitzPositroids.Edrei
