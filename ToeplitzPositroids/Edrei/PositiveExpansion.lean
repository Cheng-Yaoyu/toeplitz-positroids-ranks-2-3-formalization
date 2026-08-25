import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Strictly positive finite expansions

This small interface isolates the generic final step in tableau and path-enumeration arguments:
a quantity is a finite sum of positive weights, and the indexing family is nonempty exactly under
a combinatorial support condition.
-/

namespace ToeplitzPositroids.Edrei

/-- A finite positive expansion of `x` whose indexing type is nonempty exactly when `P` holds. -/
structure StrictPositiveExpansion (x : ℝ) (P : Prop) where
  index : Type
  indexFintype : Fintype index
  weight : index → ℝ
  weight_pos : ∀ i, 0 < weight i
  value_eq_sum : x = ∑ i, weight i
  nonempty_iff : Nonempty index ↔ P

/-- A strict positive expansion detects its support predicate exactly. -/
theorem StrictPositiveExpansion.pos_iff {x : ℝ} {P : Prop}
    (E : StrictPositiveExpansion x P) :
    0 < x ↔ P := by
  letI := E.indexFintype
  constructor
  · intro hx
    by_contra hP
    have hempty : IsEmpty E.index :=
      ⟨fun i ↦ hP (E.nonempty_iff.mp ⟨i⟩)⟩
    have hx0 : x = 0 := by
      rw [E.value_eq_sum]
      simp
    exact hx.ne' hx0
  · intro hP
    obtain ⟨i⟩ := E.nonempty_iff.mpr hP
    rw [E.value_eq_sum]
    apply Finset.sum_pos'
    · intro j _
      exact (E.weight_pos j).le
    · exact ⟨i, Finset.mem_univ i, E.weight_pos i⟩

end ToeplitzPositroids.Edrei
