import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# The partition hook condition for finite Edrei data

This file isolates the elementary partition argument in the proof of Theorem 23.
Partitions are represented by antitone natural-number sequences with the usual
zero-tail convention supplied separately by finite applications.
-/

namespace ToeplitzPositroids.Edrei

/-- A partition sequence is an antitone sequence of natural numbers. -/
def IsPartitionSequence (lambda : ℕ → ℕ) : Prop :=
  Antitone lambda

/-- The intermediate partition used in equation (10.12). -/
def hookChoice (mu lambda : ℕ → ℕ) (q : ℕ) (t : ℕ) : ℕ :=
  max (mu t) (lambda t - q)

theorem hookChoice_isPartitionSequence {mu lambda : ℕ → ℕ}
    (hmu : IsPartitionSequence mu) (hlambda : IsPartitionSequence lambda) (q : ℕ) :
    IsPartitionSequence (hookChoice mu lambda q) := by
  intro i j hij
  apply max_le
  · exact (hmu hij).trans (le_max_left _ _)
  · exact (Nat.sub_le_sub_right (hlambda hij) q).trans (le_max_right _ _)

theorem le_hookChoice (mu lambda : ℕ → ℕ) (q t : ℕ) :
    mu t ≤ hookChoice mu lambda q t :=
  le_max_left _ _

theorem hookChoice_le {mu lambda : ℕ → ℕ} (q t : ℕ) (hsub : mu t ≤ lambda t) :
    hookChoice mu lambda q t ≤ lambda t := by
  exact max_le hsub (Nat.sub_le _ _)

theorem hookChoice_rowResidual_le (mu lambda : ℕ → ℕ) (q t : ℕ) :
    lambda t - hookChoice mu lambda q t ≤ q := by
  have h : lambda t - q ≤ hookChoice mu lambda q t := le_max_right _ _
  omega

/-- The explicit choice satisfies the column-height condition exactly when the
partition hook inequality holds. -/
theorem hookChoice_shift_le {mu lambda : ℕ → ℕ}
    (hmu : IsPartitionSequence mu) {p q t : ℕ}
    (hhook : lambda (t + p) ≤ mu t + q) :
    hookChoice mu lambda q (t + p) ≤ mu t := by
  apply max_le
  · exact hmu (Nat.le_add_right t p)
  · omega

/-- Existence of an intermediate partition with the two finite-variable strip
conditions is equivalent to the hook inequality.

This is the abstract zero-tail form of equations (10.10)--(10.12).
-/
theorem exists_intermediatePartition_iff_hook
    {mu lambda : ℕ → ℕ} (hmu : IsPartitionSequence mu)
    (hlambda : IsPartitionSequence lambda) (hcontained : ∀ t, mu t ≤ lambda t)
    (p q : ℕ) :
    (∃ nu : ℕ → ℕ,
        IsPartitionSequence nu ∧
        (∀ t, mu t ≤ nu t) ∧
        (∀ t, nu t ≤ lambda t) ∧
        (∀ t, lambda t - nu t ≤ q) ∧
        (∀ t, nu (t + p) ≤ mu t)) ↔
      ∀ t, lambda (t + p) ≤ mu t + q := by
  constructor
  · rintro ⟨nu, -, -, hnuLambda, hrow, hcolumn⟩ t
    have hle := hnuLambda (t + p)
    have hres := hrow (t + p)
    have hcol := hcolumn t
    omega
  · intro hhook
    refine ⟨hookChoice mu lambda q,
      hookChoice_isPartitionSequence hmu hlambda q, ?_, ?_, ?_, ?_⟩
    · exact fun t ↦ le_hookChoice mu lambda q t
    · exact fun t ↦ hookChoice_le q t (hcontained t)
    · exact fun t ↦ hookChoice_rowResidual_le mu lambda q t
    · exact fun t ↦ hookChoice_shift_le hmu (hhook t)

end ToeplitzPositroids.Edrei
