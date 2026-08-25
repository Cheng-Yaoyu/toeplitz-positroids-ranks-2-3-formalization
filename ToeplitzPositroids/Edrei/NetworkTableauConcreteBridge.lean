import ToeplitzPositroids.Edrei.FiniteFactorConcreteBridge
import ToeplitzPositroids.Edrei.NetworkTableauWeightBridge
import ToeplitzPositroids.Edrei.TableauSupport

/-!
# Packaging the canonical network/tableau map

The weighted part of the network/tableau correspondence is unconditional.  This file packages
the remaining set-theoretic obligation as the bijectivity of the canonical map, so that no weight
identity is repeated when the converse path construction is supplied.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- The canonical map from good reflected network terms to concrete coproduct tableaux. -/
def canonicalGoodTableauMap
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J} :
    {x : TupleFiniteFactorNetworkTerm D I J hstruct // NetworkTermGood x} →
      TupleCoproductTableau (p := p) (q := q) I J hstruct :=
  fun x ↦ tupleCoproductTableauOfPathFamily x

/-- A bijective canonical map supplies the concrete finite-factor LGV bridge. -/
noncomputable def ConcreteFiniteFactorLGV.ofCanonicalBijection
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (hgamma : D.gamma = 0)
    (hbij : Function.Bijective (@canonicalGoodTableauMap p q r D I J hstruct))
    (hnonempty : Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) ↔
      HasIntermediateStripPartition I J p q) :
    ConcreteFiniteFactorLGV D I J hstruct := by
  let L := tupleNetworkLGVExpansion D hgamma I J hstruct
  let E : {x : L.term // L.good x} ≃
      TupleCoproductTableau (p := p) (q := q) I J hstruct := by
    exact Equiv.ofBijective canonicalGoodTableauMap hbij
  refine
    { gamma_eq_zero := hgamma
      lgv := L
      goodEquiv := E
      good_weight := ?_
      tableau_nonempty_iff := hnonempty }
  intro x
  exact tupleNetwork_good_signedWeight_eq_canonicalTableauWeight ⟨x.1, x.2⟩

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (hgamma : D.gamma = 0)
    (hbij : Function.Bijective (@canonicalGoodTableauMap p q r D I J hstruct)) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
        tupleCoproductWeight D I J hstruct T := by
  let E := ConcreteFiniteFactorLGV.ofCanonicalBijection hgamma hbij
    (tupleCoproduct_nonempty_iff_hasIntermediateStripPartition I J hstruct)
  exact E.value_eq_tableau_sum

/-- The canonical bijection is supplied by the explicit tableau converse modules. -/
structure CanonicalGoodBijectionBridge {p q : ℕ} (D : FiniteEdreiData p q) where
  gamma_eq_zero : D.gamma = 0
  bijective : ∀ (r : ℕ) (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J),
    Function.Bijective (@canonicalGoodTableauMap p q r D I J hstruct)

noncomputable def CanonicalGoodBijectionBridge.toConcrete
    {p q : ℕ} {D : FiniteEdreiData p q}
    (B : CanonicalGoodBijectionBridge D) :
    ConcreteGammaZeroLGVBridge D where
  gamma_eq_zero := B.gamma_eq_zero
  expansion r I J hstruct :=
    ConcreteFiniteFactorLGV.ofCanonicalBijection B.gamma_eq_zero
      (B.bijective r I J hstruct)
      (tupleCoproduct_nonempty_iff_hasIntermediateStripPartition I J hstruct)

theorem CanonicalGoodBijectionBridge.finiteFactorMinor_pos_iff_indexHook
    {p q : ℕ} {D : FiniteEdreiData p q}
    (B : CanonicalGoodBijectionBridge D)
    {r : ℕ} (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q :=
  finiteFactorMinor_pos_iff_of_concreteLGV B.toConcrete I J

end

end ToeplitzPositroids.Edrei
