import ToeplitzPositroids.Edrei.SkewTableauPair
import Mathlib.Data.Finite.Sigma

/-!
# Intermediate partitions in the supersymmetric coproduct

The positive expansion sums over an intermediate partition between the inner and outer shapes,
an alpha tableau on the inner difference, and a beta tableau on the outer difference.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

/-- A partition between `inner` and `outer` in one finite rectangle. -/
structure IntermediateRectanglePartition {r w : ℕ}
    (inner outer : RectanglePartition r w) where
  middle : RectanglePartition r w
  inner_le : ∀ i, inner i ≤ middle i
  outer_ge : ∀ i, middle i ≤ outer i

namespace IntermediateRectanglePartition

theorem middle_injective {r w : ℕ} {inner outer : RectanglePartition r w} :
    Function.Injective
      (fun N : IntermediateRectanglePartition inner outer ↦ N.middle) := by
  intro N M h
  cases N
  cases M
  cases h
  rfl

instance {r w : ℕ} {inner outer : RectanglePartition r w} :
    Finite (IntermediateRectanglePartition inner outer) :=
  Finite.of_injective (fun N ↦ N.middle) middle_injective

noncomputable instance {r w : ℕ} {inner outer : RectanglePartition r w} :
    Fintype (IntermediateRectanglePartition inner outer) := Fintype.ofFinite _

/-- The inner skew shape `middle / inner`. -/
def alphaShape {r w : ℕ} {inner outer : RectanglePartition r w}
    (N : IntermediateRectanglePartition inner outer) : FiniteSkewShape r w where
  inner := inner
  outer := N.middle
  inner_le_outer := N.inner_le

/-- The outer skew shape `outer / middle`. -/
def betaShape {r w : ℕ} {inner outer : RectanglePartition r w}
    (N : IntermediateRectanglePartition inner outer) : FiniteSkewShape r w where
  inner := N.middle
  outer := outer
  inner_le_outer := N.outer_ge

end IntermediateRectanglePartition

/-- One concrete term of the supersymmetric skew coproduct. -/
structure SupersymmetricCoproductTableau {r w p q : ℕ}
    (inner outer : RectanglePartition r w) where
  intermediate : IntermediateRectanglePartition inner outer
  tableaux : SupersymmetricSkewTableauPair (p := p) (q := q)
    intermediate.alphaShape intermediate.betaShape

namespace SupersymmetricCoproductTableau

instance {r w p q : ℕ} {inner outer : RectanglePartition r w} :
    Finite (SupersymmetricCoproductTableau (p := p) (q := q) inner outer) := by
  let E := Σ N : IntermediateRectanglePartition inner outer,
    SupersymmetricSkewTableauPair (p := p) (q := q) N.alphaShape N.betaShape
  let encode : SupersymmetricCoproductTableau (p := p) (q := q) inner outer → E :=
    fun T ↦ Sigma.mk T.intermediate T.tableaux
  apply Finite.of_injective encode
  intro T U h
  cases T
  cases U
  change Sigma.mk _ _ = Sigma.mk _ _ at h
  cases h
  rfl

noncomputable instance {r w p q : ℕ} {inner outer : RectanglePartition r w} :
    Fintype (SupersymmetricCoproductTableau (p := p) (q := q) inner outer) :=
  Fintype.ofFinite _

/-- The positive alpha/beta monomial of a coproduct term. -/
def weight {r w p q : ℕ} {inner outer : RectanglePartition r w}
    (D : FiniteEdreiData p q)
    (T : SupersymmetricCoproductTableau (p := p) (q := q) inner outer) : ℝ :=
  T.tableaux.weight D

theorem weight_pos {r w p q : ℕ} {inner outer : RectanglePartition r w}
    (D : FiniteEdreiData p q)
    (T : SupersymmetricCoproductTableau (p := p) (q := q) inner outer) :
    0 < weight D T :=
  T.tableaux.weight_pos D

/-- Every concrete coproduct term satisfies the two finite-alphabet strip bounds. -/
theorem strip_bounds {r w p q : ℕ} {inner outer : RectanglePartition r w}
    (T : SupersymmetricCoproductTableau (p := p) (q := q) inner outer) :
    T.intermediate.alphaShape.FitsColumnBound p ∧
      T.intermediate.betaShape.FitsRowBound q :=
  ⟨T.tableaux.alphaTableau.fitsColumnBound,
    T.tableaux.betaTableau.fitsRowBound⟩

/-- The concrete coproduct family is nonempty exactly when some intermediate partition satisfies
the two finite-alphabet shape bounds. -/
theorem nonempty_iff_exists_intermediate {r w p q : ℕ}
    {inner outer : RectanglePartition r w} :
    Nonempty (SupersymmetricCoproductTableau (p := p) (q := q) inner outer) ↔
      ∃ N : IntermediateRectanglePartition inner outer,
        N.alphaShape.FitsColumnBound p ∧ N.betaShape.FitsRowBound q := by
  constructor
  · rintro ⟨T⟩
    exact ⟨T.intermediate, T.strip_bounds⟩
  · rintro ⟨N, hcol, hrow⟩
    exact ⟨⟨N, ⟨AlphaSkewTableau.ofFitsColumnBound hcol,
      BetaSkewTableau.ofFitsRowBound hrow⟩⟩⟩

end SupersymmetricCoproductTableau

end ToeplitzPositroids.Edrei
