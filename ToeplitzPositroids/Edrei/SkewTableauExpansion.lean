import ToeplitzPositroids.Edrei.SkewTableauFromTuple
import ToeplitzPositroids.Edrei.SkewTableauLGV

/-!
# Concrete LGV-to-tableau bridge

This module replaces the abstract positive-expansion interface by concrete finite skew tableaux.
An implementation of the finite-factor network supplies `lgv`; its cancellation field is the
first-intersection tail-swap involution.  The remaining fields identify disjoint paths with the
tableau coproduct terms.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

/-- Concrete LGV data for one structurally admissible finite-factor minor. -/
structure ConcreteFiniteFactorLGV
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) where
  gamma_eq_zero : D.gamma = 0
  lgv : LGVExpansion (FiniteEdreiData.finiteFactorMinor D I J)
  goodEquiv : {x : lgv.term // lgv.good x} ≃
    TupleCoproductTableau (p := p) (q := q) I J hstruct
  good_weight : ∀ x, lgv.signedWeight x.val =
    tupleCoproductWeight D I J hstruct (goodEquiv x)
  tableau_nonempty_iff :
    Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) ↔
      HasIntermediateStripPartition I J p q

namespace ConcreteFiniteFactorLGV

/-- LGV cancellation and the path/tableau bijection give the supersymmetric tableau sum. -/
theorem value_eq_tableau_sum
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (E : ConcreteFiniteFactorLGV D I J hstruct) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
        tupleCoproductWeight D I J hstruct T := by
  rw [E.lgv.eq_sum_good]
  unfold LGVExpansion.goodSum
  letI := E.lgv.termFintype
  letI := E.lgv.goodDecidable
  calc
    (∑ x : {x : E.lgv.term // E.lgv.good x}, E.lgv.signedWeight x.val) =
        ∑ x : {x : E.lgv.term // E.lgv.good x},
          tupleCoproductWeight D I J hstruct (E.goodEquiv x) := by
      apply Fintype.sum_congr
      exact fun x ↦ E.good_weight x
    _ = ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
          tupleCoproductWeight D I J hstruct T :=
      E.goodEquiv.sum_comp (tupleCoproductWeight D I J hstruct)

/-- Concrete LGV data construct the positive expansion required by Theorem 23. -/
noncomputable def toFiniteFactorTableauExpansion
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (E : ConcreteFiniteFactorLGV D I J hstruct) :
    FiniteFactorTableauExpansion D I J where
  gamma_eq_zero := E.gamma_eq_zero
  expansion :=
    { index := TupleCoproductTableau (p := p) (q := q) I J hstruct
      indexFintype := inferInstance
      weight := tupleCoproductWeight D I J hstruct
      weight_pos := tupleCoproductWeight_pos D I J hstruct
      value_eq_sum := E.value_eq_tableau_sum
      nonempty_iff := by
        rw [E.tableau_nonempty_iff]
        exact ⟨fun h ↦ ⟨hstruct, h⟩, fun h ↦ h.2⟩ }

end ConcreteFiniteFactorLGV

/-- A concrete gamma-zero LGV construction for every structurally allowed minor. -/
structure ConcreteGammaZeroLGVBridge {p q : ℕ} (D : FiniteEdreiData p q) where
  gamma_eq_zero : D.gamma = 0
  expansion : ∀ (r : ℕ) (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J), ConcreteFiniteFactorLGV D I J hstruct

/-- Concrete network data eliminate the abstract packaged-expansion gap. -/
noncomputable def ConcreteGammaZeroLGVBridge.toTableauBridge
    {p q : ℕ} {D : FiniteEdreiData p q} (B : ConcreteGammaZeroLGVBridge D) :
    GammaZeroTableauBridge D := by
  intro r I J
  by_cases hstruct : StructurallyAdmissible I J
  · exact (B.expansion r I J hstruct).toFiniteFactorTableauExpansion
  · refine
      { gamma_eq_zero := B.gamma_eq_zero
        expansion :=
          { index := PEmpty
            indexFintype := inferInstance
            weight := fun x : PEmpty ↦ nomatch x
            weight_pos := fun x : PEmpty ↦ nomatch x
            value_eq_sum := by
              rw [FiniteEdreiData.finiteFactorMinor_eq_zero_of_not_structural D I J hstruct]
              simp
            nonempty_iff := by simp [hstruct] } }

/-- A concrete network construction proves the gamma-zero branch of Theorem 23 outright. -/
theorem finiteFactorMinor_pos_iff_of_concreteLGV
    {p q : ℕ} {D : FiniteEdreiData p q} (B : ConcreteGammaZeroLGVBridge D)
    {r : ℕ} (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q :=
  FiniteEdreiData.finiteFactorMinor_pos_iff_indexHook D B.toTableauBridge I J

end ToeplitzPositroids.Edrei
