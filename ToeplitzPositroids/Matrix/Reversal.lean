import ToeplitzPositroids.Matrix.Configuration
import Mathlib.Data.Fin.Rev

/-!
# Simultaneous row and column reversal

Reversing both axes contributes the same permutation sign twice to every square
minor, so all ordered minor values are preserved after reversing the selected
indices.  This is the sign-cancellation principle used repeatedly in the paper.
-/

namespace ToeplitzPositroids

variable {R : Type*} {m n : ℕ}

/-- Reverse a matrix simultaneously in its row and column directions. -/
def reverseMatrix (A : Matrix (Fin m) (Fin n) R) : Matrix (Fin m) (Fin n) R :=
  A.submatrix Fin.rev Fin.rev

@[simp]
theorem reverseMatrix_apply (A : Matrix (Fin m) (Fin n) R) (i : Fin m) (j : Fin n) :
    reverseMatrix A i j = A i.rev j.rev :=
  rfl

/-- Reverse the image of an increasing finite selection while keeping its domain
in increasing order. -/
def reverseOrderEmbedding {k m : ℕ} (f : Fin k ↪o Fin m) : Fin k ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun i ↦ (f i.rev).rev) <| by
    intro i j hij
    have hji : j.rev < i.rev := Fin.rev_lt_rev.mpr hij
    exact Fin.rev_lt_rev.mpr (f.strictMono hji)

@[simp]
theorem reverseOrderEmbedding_apply {k m : ℕ} (f : Fin k ↪o Fin m) (i : Fin k) :
    reverseOrderEmbedding f i = (f i.rev).rev :=
  rfl

@[simp]
theorem reverseOrderEmbedding_reverseOrderEmbedding {k m : ℕ} (f : Fin k ↪o Fin m) :
    reverseOrderEmbedding (reverseOrderEmbedding f) = f := by
  apply RelEmbedding.ext
  intro i
  simp

@[simp]
theorem reverseOrderEmbedding_allRows (m : ℕ) :
    reverseOrderEmbedding (allRows m) = allRows m := by
  apply RelEmbedding.ext
  intro i
  simp [allRows]

/-- Simultaneous reversal preserves an ordered minor after reversing both
increasing selections. -/
theorem orderedMinor_reverseMatrix [CommRing R] (A : Matrix (Fin m) (Fin n) R) {k : ℕ}
    (rows : Fin k ↪o Fin m) (cols : Fin k ↪o Fin n) :
    orderedMinor (reverseMatrix A) rows cols =
      orderedMinor A (reverseOrderEmbedding rows) (reverseOrderEmbedding cols) := by
  unfold orderedMinor
  calc
    ((reverseMatrix A).submatrix rows cols).det =
        ((A.submatrix (reverseOrderEmbedding rows) (reverseOrderEmbedding cols)).submatrix
          Fin.revPerm Fin.revPerm).det := by
      congr 1
      ext i j
      simp [reverseMatrix]
    _ = (A.submatrix (reverseOrderEmbedding rows) (reverseOrderEmbedding cols)).det :=
      Matrix.det_submatrix_equiv_self Fin.revPerm _

@[simp]
theorem reverseMatrix_reverseMatrix (A : Matrix (Fin m) (Fin n) R) :
    reverseMatrix (reverseMatrix A) = A := by
  ext i j
  simp [reverseMatrix]

section Ordered

variable [CommRing R] [PartialOrder R]

/-- Simultaneous reversal preserves total nonnegativity through every fixed order. -/
theorem TNUpTo.reverseMatrix {A : Matrix (Fin m) (Fin n) R} {k : ℕ}
    (hA : TNUpTo A k) : TNUpTo (reverseMatrix A) k := by
  intro l hl rows cols
  rw [orderedMinor_reverseMatrix]
  exact hA.orderedMinor_nonneg hl (reverseOrderEmbedding rows) (reverseOrderEmbedding cols)

/-- Simultaneous reversal preserves total nonnegativity. -/
theorem TotallyNonnegative.reverseMatrix {A : Matrix (Fin m) (Fin n) R}
    (hA : TotallyNonnegative A) : TotallyNonnegative (reverseMatrix A) := by
  intro k rows cols
  rw [orderedMinor_reverseMatrix]
  exact hA.orderedMinor_nonneg (reverseOrderEmbedding rows) (reverseOrderEmbedding cols)

/-- Total nonnegativity is invariant under simultaneous reversal. -/
theorem totallyNonnegative_reverseMatrix_iff (A : Matrix (Fin m) (Fin n) R) :
    TotallyNonnegative (reverseMatrix A) ↔ TotallyNonnegative A := by
  constructor
  · intro h
    simpa only [reverseMatrix_reverseMatrix] using h.reverseMatrix
  · exact TotallyNonnegative.reverseMatrix

/-- Simultaneous reversal preserves total positivity. -/
theorem TotallyPositive.reverseMatrix {A : Matrix (Fin m) (Fin n) R}
    (hA : TotallyPositive A) : TotallyPositive (reverseMatrix A) := by
  intro k rows cols
  rw [orderedMinor_reverseMatrix]
  exact hA.orderedMinor_pos (reverseOrderEmbedding rows) (reverseOrderEmbedding cols)

end Ordered

/-- Simultaneous reversal preserves the existence of a nonzero ordered maximal minor. -/
theorem hasFullRowRank_reverseMatrix_iff (A : Matrix (Fin m) (Fin n) ℝ) :
    HasFullRowRank (reverseMatrix A) ↔ HasFullRowRank A := by
  constructor
  · rintro ⟨cols, hcols⟩
    rw [orderedMinor_reverseMatrix] at hcols
    refine ⟨reverseOrderEmbedding cols, ?_⟩
    simpa only [reverseOrderEmbedding_allRows] using hcols
  · rintro ⟨cols, hcols⟩
    refine ⟨reverseOrderEmbedding cols, ?_⟩
    rw [orderedMinor_reverseMatrix]
    simpa only [reverseOrderEmbedding_allRows,
      reverseOrderEmbedding_reverseOrderEmbedding] using hcols

end ToeplitzPositroids
