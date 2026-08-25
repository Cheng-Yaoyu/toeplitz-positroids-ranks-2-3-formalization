import ToeplitzPositroids.Edrei.FiniteFactorMinor
import ToeplitzPositroids.Edrei.SkewTableauCoproduct
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Rectangle shapes associated to increasing index tuples

The reverse-offset partitions attached to row and column tuples fit in a canonical finite
rectangle.  This file turns them into the concrete shapes used by the skew-tableau expansion.
-/

namespace ToeplitzPositroids.Edrei

/-- A canonical width bounding every entry and every associated partition part. -/
def IncreasingIndexTuple.tupleWidth {r : ℕ} (J : IncreasingIndexTuple r) : ℕ :=
  Finset.univ.sup J.value

theorem IncreasingIndexTuple.value_le_tupleWidth {r : ℕ}
    (J : IncreasingIndexTuple r) (k : Fin r) :
    J k ≤ J.tupleWidth := by
  exact Finset.le_sup (Finset.mem_univ k)

theorem IncreasingIndexTuple.associatedPart_le_tupleWidth {r : ℕ}
    (J : IncreasingIndexTuple r) (t : Fin r) :
    J.associatedPart t ≤ J.tupleWidth := by
  exact (Nat.sub_le _ _).trans (J.value_le_tupleWidth t.rev)

/-- Place an associated partition in any rectangle known to contain the original tuple. -/
def IncreasingIndexTuple.associatedRectanglePartition {r w : ℕ}
    (I : IncreasingIndexTuple r) (hbound : ∀ k, I k ≤ w) :
    RectanglePartition r w where
  rowLength t := ⟨I.associatedPart t, by
    exact Nat.lt_succ_of_le ((Nat.sub_le _ _).trans (hbound t.rev))⟩
  antitone := by
    intro t u htu
    change I.associatedPart u ≤ I.associatedPart t
    exact I.associatedPart_antitone htu

/-- The inner rectangle partition associated to a structurally contained row tuple. -/
def containedInnerPartition {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) : RectanglePartition r J.tupleWidth :=
  I.associatedRectanglePartition fun k ↦ (hstruct k).trans (J.value_le_tupleWidth k)

/-- The outer rectangle partition associated to the column tuple. -/
def containingOuterPartition {r : ℕ} (J : IncreasingIndexTuple r) :
    RectanglePartition r J.tupleWidth :=
  J.associatedRectanglePartition J.value_le_tupleWidth

/-- Structural containment becomes containment of the two rectangle partitions. -/
theorem containedInnerPartition_le_outer {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) (t : Fin r) :
    containedInnerPartition I J hstruct t ≤ containingOuterPartition J t := by
  change I.associatedPart t ≤ J.associatedPart t
  exact (IncreasingIndexTuple.associatedPart_le_iff I J t).mpr (hstruct t.rev)

/-- The concrete finite tableau family for a structurally admissible minor. -/
abbrev TupleCoproductTableau {p q r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) :=
  SupersymmetricCoproductTableau (p := p) (q := q)
    (containedInnerPartition I J hstruct) (containingOuterPartition J)

/-- Its positive alpha/beta monomial. -/
def tupleCoproductWeight {p q r : ℕ} (D : ToeplitzPositroids.FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) : ℝ :=
  T.weight D

theorem tupleCoproductWeight_pos {p q r : ℕ}
    (D : ToeplitzPositroids.FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) :
    0 < tupleCoproductWeight D I J hstruct T :=
  T.weight_pos D

end ToeplitzPositroids.Edrei
