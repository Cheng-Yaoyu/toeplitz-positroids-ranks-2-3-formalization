import ToeplitzPositroids.Edrei.Support
import ToeplitzPositroids.Edrei.TableauMixedSplice

/-!
# Unconditional gamma-zero support

The concrete tableau converse supplies the abstract bridge used by `Support.lean`, so the
Toeplitz-minor support criterion can be stated without passing that bridge as an extra argument.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

theorem FiniteEdreiData.toeplitzMinor_pos_iff_minorSupportCondition_of_explicit_gamma_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    {r : ℕ} (rows cols : Fin r ↪o ℕ) :
    0 < D.toeplitzMinor rows cols ↔ D.MinorSupportCondition rows cols :=
  FiniteEdreiData.toeplitzMinor_pos_iff_minorSupportCondition_of_gamma_zero D hgamma
    ((canonicalGoodBijectionBridge_gamma_zero D hgamma).toConcrete.toTableauBridge)
    rows cols

/-- At gamma zero the full coefficient sequence is literally the finite alpha/beta-factor
sequence. -/
theorem FiniteEdreiData.coefficient_eq_finiteFactorSequence_of_gamma_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) :
    D.coefficient = D.finiteFactorSequence := by
  funext k
  by_cases hk : 0 ≤ k
  · rw [FiniteEdreiData.coefficient, if_pos hk, FiniteEdreiData.finiteFactorSequence,
      zeroExtendedNaturalSequence, if_pos hk,
      FiniteEdreiData.natCoefficient_eq_finiteFactorCoefficient D hgamma]
    rfl
  · rw [FiniteEdreiData.coefficient, if_neg hk, FiniteEdreiData.finiteFactorSequence,
      zeroExtendedNaturalSequence, if_neg hk]

/-- Hence every gamma-zero Toeplitz minor is the corresponding finite-factor-only minor. -/
theorem FiniteEdreiData.toeplitzMinor_eq_finiteFactorOnlyMinor_of_gamma_zero
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (rows cols : Fin r ↪o ℕ) :
    D.toeplitzMinor rows cols = D.finiteFactorOnlyMinor rows cols := by
  rw [FiniteEdreiData.toeplitzMinor, FiniteEdreiData.finiteFactorOnlyMinor,
    FiniteEdreiData.coefficient_eq_finiteFactorSequence_of_gamma_zero D hgamma]

/-- All gamma-zero Edrei Toeplitz minors are nonnegative. -/
theorem FiniteEdreiData.toeplitzMinor_nonneg_of_gamma_zero
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (rows cols : Fin r ↪o ℕ) :
    0 ≤ D.toeplitzMinor rows cols := by
  rw [FiniteEdreiData.toeplitzMinor_eq_finiteFactorOnlyMinor_of_gamma_zero D hgamma]
  exact D.finiteFactorMinorsNonnegative rows cols

/-- Corollary 24 without an abstract bridge parameter: the first-row-block basis predicate is
exactly the hook-condition predicate. -/
theorem FiniteEdreiData.firstRowBlockBasisPredicate_eq_selectionHookCondition_of_explicit_gamma_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) (r n : ℕ) :
    D.FirstRowBlockBasisPredicate r n =
      (fun J : Fin r ↪o Fin n ↦ SelectionHookCondition J p q) :=
  FiniteEdreiData.firstRowBlockBasisPredicate_eq_selectionHookCondition_of_gamma_zero
    D hgamma ((canonicalGoodBijectionBridge_gamma_zero D hgamma).toConcrete.toTableauBridge) r n

/-- Unconditional Schubert-cardinality form of Corollary 24 in the gamma-zero branch. -/
theorem FiniteEdreiData.firstRowBlockBasisPredicate_eq_schubert_of_gamma_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) (r n : ℕ) :
    D.FirstRowBlockBasisPredicate r n = SchubertBasisPredicate r n p q := by
  rw [FiniteEdreiData.firstRowBlockBasisPredicate_eq_selectionHookCondition_of_explicit_gamma_zero
    D hgamma]
  funext J
  apply propext
  exact selectionHookCondition_iff_cardinality_all J p q

/-- The zero-gamma first-row block is uniform when the number of alpha variables is at least the
rank. -/
theorem FiniteEdreiData.firstRowBlockBasisPredicate_eq_uniform_of_gamma_zero_of_rank_le_p
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (r n : ℕ) (hrp : r ≤ p) :
    D.FirstRowBlockBasisPredicate r n = UniformBasisPredicate r n := by
  rw [FiniteEdreiData.firstRowBlockBasisPredicate_eq_schubert_of_gamma_zero D hgamma,
    schubertBasisPredicate_eq_uniform_of_rank_le_p r n p q hrp]

/-- The zero-gamma first-row block is uniform when `q` is at least the codimension. -/
theorem FiniteEdreiData.firstRowBlockBasisPredicate_eq_uniform_of_gamma_zero_of_codimension_le_q
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (r n : ℕ) (hq : n - r ≤ q) :
    D.FirstRowBlockBasisPredicate r n = UniformBasisPredicate r n := by
  rw [FiniteEdreiData.firstRowBlockBasisPredicate_eq_schubert_of_gamma_zero D hgamma,
    schubertBasisPredicate_eq_uniform_of_codimension_le_q r n p q hq]

end

end ToeplitzPositroids.Edrei
