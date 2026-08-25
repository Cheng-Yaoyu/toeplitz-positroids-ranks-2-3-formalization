import ToeplitzPositroids.Edrei.SkewTableau
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Sign-reversing cancellation for LGV expansions

This file supplies the algebraic cancellation core of the Lindström--Gessel--Viennot argument.
Concrete path families only have to define the first-intersection tail swap and prove that it
negates signed weight.
-/

namespace ToeplitzPositroids.Edrei

/-- A fixed-point-free sign-reversing involution on the bad terms of a finite expansion. -/
structure SignReversingInvolution (term : Type) [Fintype term]
    (bad : term → Prop) [DecidablePred bad] (signedWeight : term → ℝ) where
  swap : {x : term // bad x} ≃ {x : term // bad x}
  involutive : ∀ x, swap (swap x) = x
  weight_neg : ∀ x, signedWeight (swap x).val = -signedWeight x.val

/-- Bad LGV terms cancel in pairs. -/
theorem SignReversingInvolution.sum_eq_zero
    {term : Type} [Fintype term] {bad : term → Prop} [DecidablePred bad]
    {signedWeight : term → ℝ}
    (C : SignReversingInvolution term bad signedWeight) :
    ∑ x : {x : term // bad x}, signedWeight x.val = 0 := by
  let S := ∑ x : {x : term // bad x}, signedWeight x.val
  have hperm : S = ∑ x : {x : term // bad x}, signedWeight (C.swap x).val := by
    exact (C.swap.sum_comp (fun x ↦ signedWeight x.val)).symm
  have hneg : (∑ x : {x : term // bad x}, signedWeight (C.swap x).val) = -S := by
    simp [C.weight_neg, S]
  change S = 0
  linarith

/-- Abstract finite LGV data: the determinant/Leibniz expansion is a sum over all path terms,
while the good terms are the vertex-disjoint families. -/
structure LGVExpansion (value : ℝ) where
  term : Type
  termFintype : Fintype term
  good : term → Prop
  goodDecidable : DecidablePred good
  signedWeight : term → ℝ
  value_eq_sum : value = ∑ x, signedWeight x
  cancellation : SignReversingInvolution term (fun x ↦ ¬good x) signedWeight

/-- The finite sum of the good (vertex-disjoint) terms. -/
noncomputable def LGVExpansion.goodSum {value : ℝ} (E : LGVExpansion value) : ℝ := by
  letI := E.termFintype
  letI := E.goodDecidable
  exact ∑ x : {x : E.term // E.good x}, E.signedWeight x.val

/-- After sign-reversing cancellation, only good path families remain. -/
theorem LGVExpansion.eq_sum_good {value : ℝ} (E : LGVExpansion value) :
    value = E.goodSum := by
  letI := E.termFintype
  letI := E.goodDecidable
  have hbad := E.cancellation.sum_eq_zero
  calc
    value = ∑ x : E.term, E.signedWeight x := E.value_eq_sum
    _ = (∑ x : {x : E.term // E.good x}, E.signedWeight x.val) +
        ∑ x : {x : E.term // ¬E.good x}, E.signedWeight x.val :=
      (Fintype.sum_subtype_add_sum_subtype E.good E.signedWeight).symm
    _ = ∑ x : {x : E.term // E.good x}, E.signedWeight x.val := by rw [hbad, add_zero]
    _ = E.goodSum := by rfl

end ToeplitzPositroids.Edrei
