import ToeplitzPositroids.Matrix.Configuration
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Total nonnegativity for three-row matrices

For a matrix with three rows, the only minors not covered by `TNUpTo A 2` are
the maximal minors.  This elementary reduction is used by the convex-chain
criterion.
-/

namespace ToeplitzPositroids

variable {n : ℕ}

/-- An order embedding from `Fin 3` to itself is the identity embedding. -/
theorem finThree_orderEmbedding_eq_allRows (rows : Fin 3 ↪o Fin 3) :
    rows = allRows 3 := by
  apply RelEmbedding.ext
  intro i
  fin_cases i
  · apply Fin.ext
    change (rows 0).val = 0
    have h1 : rows 0 < rows 1 := rows.strictMono (by decide)
    have h2 : rows 1 < rows 2 := rows.strictMono (by decide)
    omega
  · apply Fin.ext
    change (rows 1).val = 1
    have h0 : rows 0 < rows 1 := rows.strictMono (by decide)
    have h1 : rows 1 < rows 2 := rows.strictMono (by decide)
    omega
  · apply Fin.ext
    change (rows 2).val = 2
    have h0 : rows 0 < rows 1 := rows.strictMono (by decide)
    have h1 : rows 1 < rows 2 := rows.strictMono (by decide)
    omega

/-- A three-row matrix is totally nonnegative exactly when its minors through
order two and all of its maximal minors are nonnegative. -/
theorem totallyNonnegative_fin_three_iff
    (A : Matrix (Fin 3) (Fin n) ℝ) :
    TotallyNonnegative A ↔ TNUpTo A 2 ∧ MaximalMinorsNonnegative A := by
  constructor
  · intro hA
    exact ⟨hA.tnUpTo 2, fun cols ↦ hA.orderedMinor_nonneg (allRows 3) cols⟩
  · rintro ⟨hTwo, hMax⟩ k rows cols
    have hk : k ≤ 3 := by
      simpa using Fintype.card_le_of_injective rows rows.injective
    by_cases hkTwo : k ≤ 2
    · exact hTwo.orderedMinor_nonneg hkTwo rows cols
    · have hkThree : k = 3 := by omega
      subst k
      rw [finThree_orderEmbedding_eq_allRows rows]
      exact hMax cols

end ToeplitzPositroids
