import ToeplitzPositroids.Edrei.GammaZeroSupport
import ToeplitzPositroids.Matrix.Positroid

/-!
# The finite Edrei first-row-block positroid

This file packages Corollary 24 as a statement about the genuine column matroid of the finite
Toeplitz section.  In particular, the Schubert and uniform conclusions no longer stop at an
auxiliary basis predicate.
-/

namespace ToeplitzPositroids

open Set

noncomputable section

namespace FiniteEdreiData

open ToeplitzPositroids.Edrei.FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- Every Toeplitz minor of finite Edrei data is nonnegative. -/
theorem toeplitzMinor_nonneg {r : ℕ} (rows cols : Fin r ↪o ℕ) :
    0 ≤ D.toeplitzMinor rows cols := by
  by_cases hzero : D.gamma = 0
  · exact Edrei.FiniteEdreiData.toeplitzMinor_nonneg_of_gamma_zero D hzero rows cols
  · have hgamma : 0 < D.gamma := lt_of_le_of_ne D.gamma_nonneg (Ne.symm hzero)
    by_cases hallowed : ∀ i, rows i ≤ cols i
    · exact (D.toeplitzMinor_pos_iff_componentwise_le_of_gamma_pos
        hgamma rows cols).mpr hallowed |>.le
    · rw [D.toeplitzMinor_eq_zero_of_not_componentwise_le rows cols hallowed]

/-- An ordered minor of a finite Toeplitz section is the corresponding natural-indexed Edrei
Toeplitz minor. -/
theorem orderedMinor_finiteToeplitzSection_eq_toeplitzMinor
    {r n k : ℕ} (rows : Fin k ↪o Fin r) (cols : Fin k ↪o Fin n) :
    orderedMinor (D.finiteToeplitzSection r n) rows cols =
      D.toeplitzMinor (finiteSelectionNatural rows) (finiteSelectionNatural cols) := by
  rfl

/-- Every finite Edrei Toeplitz section is totally nonnegative in all minor orders. -/
theorem finiteToeplitzSection_totallyNonnegative (r n : ℕ) :
    TotallyNonnegative (D.finiteToeplitzSection r n) := by
  intro k rows cols
  rw [D.orderedMinor_finiteToeplitzSection_eq_toeplitzMinor rows cols]
  exact D.toeplitzMinor_nonneg _ _

/-- The ordered maximal minor on a first-row-block column selection is the minor used in the
support predicate of Corollary 24. -/
theorem orderedMinor_finiteToeplitzSection_allRows_eq_firstRowBlockMinor
    {r n : ℕ} (J : Fin r ↪o Fin n) :
    orderedMinor (D.finiteToeplitzSection r n) (allRows r) J =
      D.firstRowBlockMinor J := by
  rw [D.orderedMinor_finiteToeplitzSection_eq_toeplitzMinor]
  have hrows : finiteSelectionNatural (allRows r) = firstNaturalRows r := by
    apply RelEmbedding.ext
    intro i
    rfl
  rw [hrows]
  rfl

/-- When `r ≤ n`, the principal first `r` columns witness full row rank. -/
theorem finiteToeplitzSection_hasFullRowRank {r n : ℕ} (hrn : r ≤ n) :
    HasFullRowRank (D.finiteToeplitzSection r n) := by
  let J : Fin r ↪o Fin n := Fin.castLEOrderEmb hrn
  refine ⟨J, ?_⟩
  rw [D.orderedMinor_finiteToeplitzSection_allRows_eq_firstRowBlockMinor]
  unfold firstRowBlockMinor
  have hcols : finiteSelectionNatural J = firstNaturalRows r := by
    apply RelEmbedding.ext
    intro i
    rfl
  rw [hcols, D.toeplitzMinor_principal]
  norm_num

/-- The actual positroid representation carried by the first `r` rows and first `n` columns. -/
def firstRowBlockPositroidRepresentation {r n : ℕ} (hrn : r ≤ n) :
    PositroidRepresentation r n where
  matrix := D.finiteToeplitzSection r n
  isPositroidRepresentation :=
    ⟨D.finiteToeplitzSection_hasFullRowRank hrn,
      (D.finiteToeplitzSection_totallyNonnegative r n).maximalMinorsNonnegative⟩

/-- Its genuine column-matroid bases are exactly the positive first-row-block minors. -/
theorem firstRowBlockPositroid_isBase_range_iff
    {r n : ℕ} (hrn : r ≤ n) (J : Fin r ↪o Fin n) :
    (D.firstRowBlockPositroidRepresentation hrn).matroid.IsBase (Set.range J) ↔
      D.FirstRowBlockBasisPredicate r n J := by
  rw [(D.firstRowBlockPositroidRepresentation hrn).isBase_range_iff_orderedMinor_pos]
  change 0 < orderedMinor (D.finiteToeplitzSection r n) (allRows r) J ↔ _
  rw [D.orderedMinor_finiteToeplitzSection_allRows_eq_firstRowBlockMinor]
  rfl

end FiniteEdreiData

namespace Edrei

/-- A rank-`r` matroid on `Fin n` has the Schubert basis support from Corollary 24. -/
def HasSchubertBasisSupport {n : ℕ} (M : Matroid (Fin n)) (r p q : ℕ) : Prop :=
  M.E = Set.univ ∧
    ∀ J : Fin r ↪o Fin n,
      M.IsBase (Set.range J) ↔ SchubertBasisPredicate r n p q J

/-- A rank-`r` matroid on `Fin n` has uniform basis support. -/
def HasUniformBasisSupport {n : ℕ} (M : Matroid (Fin n)) (r : ℕ) : Prop :=
  M.E = Set.univ ∧
    ∀ J : Fin r ↪o Fin n, M.IsBase (Set.range J)

end Edrei

namespace FiniteEdreiData

open ToeplitzPositroids.Edrei.FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- Corollary 24 as a theorem about the represented column matroid: at gamma zero its bases are
exactly those satisfying the Schubert cardinality condition. -/
theorem firstRowBlockPositroid_hasSchubertBasisSupport_of_gamma_zero
    {r n : ℕ} (hrn : r ≤ n) (hgamma : D.gamma = 0) :
    Edrei.HasSchubertBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r p q := by
  constructor
  · exact (D.firstRowBlockPositroidRepresentation hrn).matroid_ground
  · intro J
    rw [D.firstRowBlockPositroid_isBase_range_iff hrn]
    have hpred := Edrei.FiniteEdreiData.firstRowBlockBasisPredicate_eq_schubert_of_gamma_zero
      D hgamma r n
    exact Eq.to_iff (congrFun hpred J)

private theorem firstRowBlockPositroid_hasUniformBasisSupport_of_predicate_eq
    {r n : ℕ} (hrn : r ≤ n)
    (hpred : D.FirstRowBlockBasisPredicate r n = Edrei.UniformBasisPredicate r n) :
    Edrei.HasUniformBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r := by
  constructor
  · exact (D.firstRowBlockPositroidRepresentation hrn).matroid_ground
  · intro J
    rw [D.firstRowBlockPositroid_isBase_range_iff hrn]
    have hJ := congrFun hpred J
    simpa [Edrei.UniformBasisPredicate] using hJ

/-- The first-row-block positroid is uniform when `p ≥ r` in the gamma-zero branch. -/
theorem firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_zero_of_rank_le_p
    {r n : ℕ} (hrn : r ≤ n) (hgamma : D.gamma = 0) (hrp : r ≤ p) :
    Edrei.HasUniformBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r :=
  D.firstRowBlockPositroid_hasUniformBasisSupport_of_predicate_eq hrn
    (firstRowBlockBasisPredicate_eq_uniform_of_gamma_zero_of_rank_le_p
      D hgamma r n hrp)

/-- The first-row-block positroid is uniform when `q ≥ n-r` in the gamma-zero branch. -/
theorem firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_zero_of_codimension_le_q
    {r n : ℕ} (hrn : r ≤ n) (hgamma : D.gamma = 0) (hq : n - r ≤ q) :
    Edrei.HasUniformBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r :=
  D.firstRowBlockPositroid_hasUniformBasisSupport_of_predicate_eq hrn
    (firstRowBlockBasisPredicate_eq_uniform_of_gamma_zero_of_codimension_le_q
      D hgamma r n hq)

/-- A positive exponential parameter makes the represented first-row-block positroid uniform. -/
theorem firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_pos
    {r n : ℕ} (hrn : r ≤ n) (hgamma : 0 < D.gamma) :
    Edrei.HasUniformBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r :=
  D.firstRowBlockPositroid_hasUniformBasisSupport_of_predicate_eq hrn
    (D.firstRowBlockBasisPredicate_eq_uniform_of_gamma_pos hgamma r n)

/-- The three uniform cases in Corollary 24, in one statement. -/
theorem firstRowBlockPositroid_hasUniformBasisSupport
    {r n : ℕ} (hrn : r ≤ n)
    (huniform : r ≤ p ∨ n - r ≤ q ∨ 0 < D.gamma) :
    Edrei.HasUniformBasisSupport
      (D.firstRowBlockPositroidRepresentation hrn).matroid r := by
  rcases huniform with hrp | hq | hgamma
  · by_cases hzero : D.gamma = 0
    · exact D.firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_zero_of_rank_le_p
        hrn hzero hrp
    · exact D.firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_pos hrn
        (lt_of_le_of_ne D.gamma_nonneg (Ne.symm hzero))
  · by_cases hzero : D.gamma = 0
    · exact
        D.firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_zero_of_codimension_le_q
          hrn hzero hq
    · exact D.firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_pos hrn
        (lt_of_le_of_ne D.gamma_nonneg (Ne.symm hzero))
  · exact D.firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_pos hrn hgamma

/-- Corollary 24, bundled as the Schubert conclusion at gamma zero together with all three
uniform specializations for the actual represented column matroid. -/
theorem corollaryTwentyFour {r n : ℕ} (hrn : r ≤ n) :
    (D.gamma = 0 →
      Edrei.HasSchubertBasisSupport
        (D.firstRowBlockPositroidRepresentation hrn).matroid r p q) ∧
    ((r ≤ p ∨ n - r ≤ q ∨ 0 < D.gamma) →
      Edrei.HasUniformBasisSupport
        (D.firstRowBlockPositroidRepresentation hrn).matroid r) := by
  exact ⟨D.firstRowBlockPositroid_hasSchubertBasisSupport_of_gamma_zero hrn,
    D.firstRowBlockPositroid_hasUniformBasisSupport hrn⟩

end FiniteEdreiData

end


end ToeplitzPositroids
