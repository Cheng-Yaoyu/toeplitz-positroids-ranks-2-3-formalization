import ToeplitzPositroids.Edrei.IndexTuple
import Lean.Elab.Tactic.Omega

/-!
# Translation of the partition hook inequality

This file proves that the partition inequality
`λ_(t+p) ≤ μ_t + q` is exactly the Toeplitz index inequality
`j_(k-p) + p - q ≤ i_k`, written without truncated subtraction as
`j_(k-p) + p ≤ i_k + q`.
-/

namespace ToeplitzPositroids.Edrei

open IncreasingIndexTuple

/-- The partition index `t + p`, where `t < r - p`. -/
def shiftedPartitionIndex {r p : ℕ} (hp : p ≤ r) (t : Fin (r - p)) : Fin r :=
  ⟨t.val + p, by omega⟩

/-- The unshifted partition index `t`, embedded into `Fin r`. -/
def unshiftedPartitionIndex {r p : ℕ} (hp : p ≤ r) (t : Fin (r - p)) : Fin r :=
  ⟨t.val, by omega⟩

@[simp]
theorem shiftedPartitionIndex_val {r p : ℕ} (hp : p ≤ r) (t : Fin (r - p)) :
    (shiftedPartitionIndex hp t).val = t.val + p :=
  rfl

@[simp]
theorem unshiftedPartitionIndex_val {r p : ℕ} (hp : p ≤ r) (t : Fin (r - p)) :
    (unshiftedPartitionIndex hp t).val = t.val :=
  rfl

/-- The two reversed original positions differ by exactly `p`. -/
theorem reversed_hook_positions {r p : ℕ} (hp : p ≤ r) (t : Fin (r - p)) :
    (shiftedPartitionIndex hp t).rev.val + 1 + p =
      (unshiftedPartitionIndex hp t).rev.val + 1 := by
  simp [shiftedPartitionIndex, unshiftedPartitionIndex, Fin.val_rev]
  omega

/-- One partition hook inequality is equivalent to its sharp Toeplitz index
inequality. -/
theorem associatedPart_hook_iff_index_hook {r p q : ℕ} (hp : p ≤ r)
    (I J : IncreasingIndexTuple r) (t : Fin (r - p)) :
    J.associatedPart (shiftedPartitionIndex hp t) ≤
        I.associatedPart (unshiftedPartitionIndex hp t) + q ↔
      J (shiftedPartitionIndex hp t).rev + p ≤
        I (unshiftedPartitionIndex hp t).rev + q := by
  rw [associatedPart, associatedPart]
  have hJ := J.position_le (shiftedPartitionIndex hp t).rev
  have hI := I.position_le (unshiftedPartitionIndex hp t).rev
  have hpos := reversed_hook_positions hp t
  omega

/-- The complete partition-hook family and the complete Toeplitz-index family
are equivalent. -/
theorem partitionHookFamily_iff_indexHookFamily {r p q : ℕ} (hp : p ≤ r)
    (I J : IncreasingIndexTuple r) :
    (∀ t : Fin (r - p),
        J.associatedPart (shiftedPartitionIndex hp t) ≤
          I.associatedPart (unshiftedPartitionIndex hp t) + q) ↔
      ∀ t : Fin (r - p),
        J (shiftedPartitionIndex hp t).rev + p ≤
          I (unshiftedPartitionIndex hp t).rev + q := by
  constructor <;> intro h t
  · exact (associatedPart_hook_iff_index_hook hp I J t).mp (h t)
  · exact (associatedPart_hook_iff_index_hook hp I J t).mpr (h t)

/-- If `p ≥ r`, the type indexing hook inequalities is empty. -/
theorem hookIndex_isEmpty_of_le {r p : ℕ} (hrp : r ≤ p) : IsEmpty (Fin (r - p)) := by
  rw [Nat.sub_eq_zero_of_le hrp]
  infer_instance

end ToeplitzPositroids.Edrei
