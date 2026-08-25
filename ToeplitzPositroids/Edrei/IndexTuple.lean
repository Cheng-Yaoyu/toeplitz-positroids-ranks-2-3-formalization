import ToeplitzPositroids.Edrei.PartitionHook
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Lean.Elab.Tactic.Omega

/-!
# Increasing index tuples and their associated partitions

This file formalizes the index-to-partition translation in equation (10.3).
Indices are one-based natural numbers, matching the manuscript.
-/

namespace ToeplitzPositroids.Edrei

/-- A one-based increasing `r`-tuple of indices.  The `position_le` field is the
standard consequence `k + 1 ≤ i_k`, retained explicitly to simplify arithmetic
with truncated subtraction. -/
structure IncreasingIndexTuple (r : ℕ) where
  /-- The one-based indices. -/
  value : Fin r → ℕ
  /-- The indices increase strictly. -/
  strictMono : StrictMono value
  /-- The `k`-th index is at least `k + 1`. -/
  position_le : ∀ k, k.val + 1 ≤ value k

namespace IncreasingIndexTuple

instance {r : ℕ} : CoeFun (IncreasingIndexTuple r) (fun _ ↦ Fin r → ℕ) :=
  ⟨value⟩

/-- The partition associated to an increasing tuple, in reverse order. -/
def associatedPart {r : ℕ} (I : IncreasingIndexTuple r) (t : Fin r) : ℕ :=
  I t.rev - (t.rev.val + 1)

/-- Structural containment of the associated partitions is exactly componentwise
containment of the original increasing tuples. -/
theorem associatedPart_le_iff {r : ℕ} (I J : IncreasingIndexTuple r) (t : Fin r) :
    I.associatedPart t ≤ J.associatedPart t ↔ I t.rev ≤ J t.rev := by
  exact Nat.sub_le_sub_iff_right (J.position_le t.rev)

theorem associatedPart_forall_le_iff {r : ℕ} (I J : IncreasingIndexTuple r) :
    (∀ t, I.associatedPart t ≤ J.associatedPart t) ↔ ∀ k, I k ≤ J k := by
  constructor
  · intro h k
    simpa using (associatedPart_le_iff I J k.rev).mp (h k.rev)
  · intro h t
    exact (associatedPart_le_iff I J t).mpr (h t.rev)

private theorem strictMono_fin_add_le {r : ℕ} {f : Fin r → ℕ}
    (hf : StrictMono f) (i : Fin r) (k : ℕ) (hbound : i.val + k < r) :
    k + f i ≤ f ⟨i.val + k, hbound⟩ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hk : i.val + k < r := by omega
      have hprev := ih hk
      have hstep :
          f ⟨i.val + k, hk⟩ < f ⟨i.val + (k + 1), hbound⟩ := by
        apply hf
        exact Fin.mk_lt_mk.mpr (by omega)
      omega

/-- The offset sequence `i_k - k` is weakly increasing in the original order. -/
theorem offset_mono {r : ℕ} (I : IncreasingIndexTuple r) {i j : Fin r} (hij : i ≤ j) :
    I i - (i.val + 1) ≤ I j - (j.val + 1) := by
  by_cases hEq : i = j
  · subst j
    exact le_rfl
  have hij' : i < j := lt_of_le_of_ne hij hEq
  have hgap : j.val - i.val + I i ≤ I j := by
    have hadd := strictMono_fin_add_le I.strictMono i (j.val - i.val) (by
      rw [Nat.add_sub_of_le hij]
      exact j.isLt)
    have hidx : (⟨i.val + (j.val - i.val), by omega⟩ : Fin r) = j := by
      apply Fin.ext
      exact Nat.add_sub_of_le hij
    rw [hidx] at hadd
    exact hadd
  have hiPos := I.position_le i
  have hjPos := I.position_le j
  omega

/-- The associated finite partition is antitone. -/
theorem associatedPart_antitone {r : ℕ} (I : IncreasingIndexTuple r) :
    Antitone I.associatedPart := by
  intro t u htu
  apply offset_mono I
  exact Fin.rev_le_rev.mpr htu

/-- Extend an associated partition by zero beyond its finite length. -/
def associatedPartZeroTail {r : ℕ} (I : IncreasingIndexTuple r) : ℕ → ℕ :=
  fun t ↦ if ht : t < r then I.associatedPart ⟨t, ht⟩ else 0

theorem associatedPartZeroTail_apply {r : ℕ} (I : IncreasingIndexTuple r)
    {t : ℕ} (ht : t < r) :
    I.associatedPartZeroTail t = I.associatedPart ⟨t, ht⟩ := by
  simp [associatedPartZeroTail, ht]

/-- The zero-tail extension remains a partition sequence. -/
theorem associatedPartZeroTail_isPartitionSequence {r : ℕ}
    (I : IncreasingIndexTuple r) : IsPartitionSequence I.associatedPartZeroTail := by
  intro t u htu
  by_cases hu : u < r
  · have ht : t < r := lt_of_le_of_lt htu hu
    rw [associatedPartZeroTail_apply I ht, associatedPartZeroTail_apply I hu]
    exact I.associatedPart_antitone (by simpa using htu)
  · simp [associatedPartZeroTail, hu]

/-- Componentwise containment of increasing tuples is equivalent to containment
of their zero-tail partition sequences. -/
theorem associatedPartZeroTail_forall_le_iff {r : ℕ}
    (I J : IncreasingIndexTuple r) :
    (∀ t, I.associatedPartZeroTail t ≤ J.associatedPartZeroTail t) ↔
      ∀ k, I k ≤ J k := by
  constructor
  · intro h k
    have hk := h k.rev.val
    rw [associatedPartZeroTail_apply I k.rev.isLt,
      associatedPartZeroTail_apply J k.rev.isLt] at hk
    have hk' := (associatedPart_le_iff I J k.rev).mp hk
    simpa using hk'
  · intro h t
    by_cases ht : t < r
    · rw [associatedPartZeroTail_apply I ht, associatedPartZeroTail_apply J ht]
      exact (associatedPart_le_iff I J ⟨t, ht⟩).mpr (h _)
    · simp [associatedPartZeroTail, ht]

end IncreasingIndexTuple

end ToeplitzPositroids.Edrei
