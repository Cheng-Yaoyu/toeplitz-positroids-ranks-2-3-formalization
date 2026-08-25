import ToeplitzPositroids.Edrei.GammaPositiveSupport
import ToeplitzPositroids.Edrei.FiniteFactorMinor
import ToeplitzPositroids.Edrei.SchubertCondition

/-!
# The finite Edrei support theorem

This file assembles the two branches of Theorem 23 and derives the
first-row-block Schubert positroid statement of Corollary 24.
-/

namespace ToeplitzPositroids

noncomputable section

/-- Regard an increasing finite column selection as a natural-number selection. -/
def finiteSelectionNatural {r n : ℕ} (J : Fin r ↪o Fin n) : Fin r ↪o ℕ :=
  J.trans (Fin.valOrderEmb n)

@[simp]
theorem finiteSelectionNatural_apply {r n : ℕ} (J : Fin r ↪o Fin n) (i : Fin r) :
    finiteSelectionNatural J i = (J i).val :=
  rfl

/-- The maximal minor of the first `r` rows on a selected `r`-subset of
the first `n` columns. -/
def FiniteEdreiData.firstRowBlockMinor {p q r n : ℕ}
    (D : FiniteEdreiData p q) (J : Fin r ↪o Fin n) : ℝ :=
  D.toeplitzMinor (firstNaturalRows r) (finiteSelectionNatural J)

/-- The basis predicate represented by the first-row block. -/
def FiniteEdreiData.FirstRowBlockBasisPredicate {p q : ℕ}
    (D : FiniteEdreiData p q) (r n : ℕ) : (Fin r ↪o Fin n) → Prop :=
  fun J ↦ 0 < D.firstRowBlockMinor J

/-- Structural admissibility is automatic for a first-row-block selection. -/
theorem firstNaturalRows_le_finiteSelectionNatural {r n : ℕ}
    (J : Fin r ↪o Fin n) (i : Fin r) :
    firstNaturalRows r i ≤ finiteSelectionNatural J i := by
  have hpos := (Edrei.oneBasedIndexTuple J).position_le i
  change i.val + 1 ≤ (J i).val + 1 at hpos
  change i.val ≤ (J i).val
  omega

/-- Convert a zero-based increasing natural selection to the manuscript's
one-based increasing tuple. -/
def Edrei.naturalIndexTuple {r : ℕ} (I : Fin r ↪o ℕ) :
    Edrei.IncreasingIndexTuple r where
  value k := I k + 1
  strictMono := fun _ _ h ↦ Nat.add_lt_add_right (I.strictMono h) 1
  position_le := by
    intro k
    have hle : ∀ (n : ℕ) (hn : n < r), n ≤ I ⟨n, hn⟩ := by
      intro n hn
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
          have hn' : n < r := by omega
          have hstep : I ⟨n, hn'⟩ < I ⟨n + 1, hn⟩ := I.strictMono (by simp)
          exact Nat.succ_le_of_lt ((ih hn').trans_lt hstep)
    have hk : k.val ≤ I k := by simpa using hle k.val k.isLt
    omega

/-- Returning to zero-based indices recovers the original natural selection. -/
@[simp]
theorem Edrei.naturalIndexTuple_zeroBasedOrderEmbedding {r : ℕ}
    (I : Fin r ↪o ℕ) :
    (Edrei.naturalIndexTuple I).zeroBasedOrderEmbedding = I := by
  apply RelEmbedding.ext
  intro k
  simp [Edrei.naturalIndexTuple, Edrei.IncreasingIndexTuple.zeroBasedOrderEmbedding]

/-- The full-data minor and its one-based-tuple wrapper agree. -/
theorem Edrei.FiniteEdreiData.finiteFactorMinor_naturalIndexTuple {p q r : ℕ}
    (D : FiniteEdreiData p q) (I J : Fin r ↪o ℕ) :
    Edrei.FiniteEdreiData.finiteFactorMinor D
        (Edrei.naturalIndexTuple I) (Edrei.naturalIndexTuple J) =
      D.toeplitzMinor I J := by
  simp [Edrei.FiniteEdreiData.finiteFactorMinor]

/-- Structural containment of the one-based tuples is exactly componentwise
containment of their zero-based selections. -/
theorem Edrei.structurallyAdmissible_naturalIndexTuple_iff {r : ℕ}
    (I J : Fin r ↪o ℕ) :
    Edrei.StructurallyAdmissible (Edrei.naturalIndexTuple I)
        (Edrei.naturalIndexTuple J) ↔
      ∀ k, I k ≤ J k := by
  constructor
  · intro h k
    have hk := h k
    change I k + 1 ≤ J k + 1 at hk
    omega
  · intro h k
    change I k + 1 ≤ J k + 1
    exact Nat.add_le_add_right (h k) 1

/-- Increasing index tuples are determined by their value functions. -/
theorem Edrei.IncreasingIndexTuple.ext_value {r : ℕ}
    {I J : Edrei.IncreasingIndexTuple r} (h : I.value = J.value) : I = J := by
  cases I
  cases J
  cases h
  rfl

/-- The finite-selection and natural-selection one-based tuples coincide. -/
theorem Edrei.naturalIndexTuple_finiteSelectionNatural {r n : ℕ}
    (J : Fin r ↪o Fin n) :
    Edrei.naturalIndexTuple (finiteSelectionNatural J) = Edrei.oneBasedIndexTuple J := by
  apply Edrei.IncreasingIndexTuple.ext_value
  rfl

/-- The first-row one-based tuple has entries `1, ..., r`. -/
@[simp]
theorem Edrei.naturalIndexTuple_firstNaturalRows_apply {r : ℕ} (k : Fin r) :
    Edrei.naturalIndexTuple (firstNaturalRows r) k = k.val + 1 :=
  rfl

/-- For the first row block, the general index-hook inequalities are exactly
the Schubert hook family of the finite column selection. -/
theorem Edrei.indexHookInequalities_firstRowBlock_iff_selectionHookCondition
    {r n : ℕ} (J : Fin r ↪o Fin n) (p q : ℕ) :
    Edrei.IndexHookInequalities
        (Edrei.naturalIndexTuple (firstNaturalRows r))
        (Edrei.naturalIndexTuple (finiteSelectionNatural J)) p q ↔
      Edrei.SelectionHookCondition J p q := by
  constructor
  · intro h l
    let k : Fin r := ⟨l.val + p, by omega⟩
    have hkcond : p < k.val + 1 := by
      dsimp only [k]
      omega
    have hk := h k hkcond
    change (J (Edrei.hookPosition r p l)).val + 1 ≤ l.val + 1 + q
    change (J ⟨k.val - p, by omega⟩).val + 1 + p ≤ k.val + 1 + q at hk
    have hindex : (⟨k.val - p, by omega⟩ : Fin r) = Edrei.hookPosition r p l := by
      apply Fin.ext
      simp [k, Edrei.hookPosition]
    rw [hindex] at hk
    simp only [k] at hk
    omega
  · intro h k hk
    let l : Fin (r - p) := ⟨k.val - p, by omega⟩
    have hl := h l
    change (J ⟨k.val - p, by omega⟩).val + 1 + p ≤ k.val + 1 + q
    change (J (Edrei.hookPosition r p l)).val + 1 ≤ l.val + 1 + q at hl
    have hindex : Edrei.hookPosition r p l = (⟨k.val - p, by omega⟩ : Fin r) := by
      apply Fin.ext
      simp [l, Edrei.hookPosition]
    rw [hindex] at hl
    simp only [l] at hl
    omega

/-- The Schubert hook and cardinality formulations agree in every parameter
range, including the vacuous case `r ≤ p`. -/
theorem Edrei.selectionHookCondition_iff_cardinality_all {r n : ℕ}
    (J : Fin r ↪o Fin n) (p q : ℕ) :
    Edrei.SelectionHookCondition J p q ↔ Edrei.SelectionCardinalityCondition J p q := by
  by_cases hp : p < r
  · exact Edrei.selectionHookCondition_iff_cardinality J p q hp
  · have hboth := Edrei.selectionConditions_of_rank_le_p (q := q) J (Nat.le_of_not_gt hp)
    exact iff_of_true hboth.1 hboth.2

/-- The support condition in Theorem 23, expressed uniformly across the
zero-gamma and positive-gamma branches. -/
def FiniteEdreiData.MinorSupportCondition {p q r : ℕ}
    (D : FiniteEdreiData p q) (rows cols : Fin r ↪o ℕ) : Prop :=
  (∀ i, rows i ≤ cols i) ∧
    (D.gamma = 0 →
      Edrei.IndexHookInequalities (Edrei.naturalIndexTuple rows)
        (Edrei.naturalIndexTuple cols) p q)

/-- The support condition depends on gamma only through whether it vanishes. -/
theorem FiniteEdreiData.minorSupportCondition_iff_of_gamma_zero_iff
    {p q r : ℕ} (D E : FiniteEdreiData p q) (rows cols : Fin r ↪o ℕ)
    (hgamma : D.gamma = 0 ↔ E.gamma = 0) :
    D.MinorSupportCondition rows cols ↔ E.MinorSupportCondition rows cols := by
  constructor
  · rintro ⟨hstruct, hhook⟩
    exact ⟨hstruct, fun hE ↦ hhook (hgamma.mpr hE)⟩
  · rintro ⟨hstruct, hhook⟩
    exact ⟨hstruct, fun hD ↦ hhook (hgamma.mp hD)⟩

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- The unified support condition specializes to structural containment when
gamma is positive. -/
theorem toeplitzMinor_pos_iff_minorSupportCondition_of_gamma_pos
    (hgamma : 0 < D.gamma) {r : ℕ} (rows cols : Fin r ↪o ℕ) :
    0 < D.toeplitzMinor rows cols ↔ D.MinorSupportCondition rows cols := by
  rw [D.toeplitzMinor_pos_iff_componentwise_le_of_gamma_pos hgamma]
  simp [MinorSupportCondition, hgamma.ne']

/-- The zero-gamma support criterion, conditional on the concrete finite-factor tableau bridge. -/
theorem toeplitzMinor_pos_iff_minorSupportCondition_of_gamma_zero
    (hgamma : D.gamma = 0) (hbridge : Edrei.GammaZeroTableauBridge D)
    {r : ℕ} (rows cols : Fin r ↪o ℕ) :
    0 < D.toeplitzMinor rows cols ↔ D.MinorSupportCondition rows cols := by
  let I := Edrei.naturalIndexTuple rows
  let J := Edrei.naturalIndexTuple cols
  have hminor := Edrei.FiniteEdreiData.finiteFactorMinor_pos_iff_indexHook D hbridge I J
  have hconvert := Edrei.structurallyAdmissible_naturalIndexTuple_iff rows cols
  rw [← Edrei.FiniteEdreiData.finiteFactorMinor_naturalIndexTuple D rows cols]
  simpa [I, J, MinorSupportCondition] using
    (show Edrei.FiniteEdreiData.finiteFactorMinor D I J > 0 ↔
      Edrei.StructurallyAdmissible I J ∧ Edrei.IndexHookInequalities I J p q from hminor).trans
      (by
        constructor
        · rintro ⟨hstruct, hhook⟩
          exact ⟨hconvert.mp hstruct, fun _ ↦ hhook⟩
        · rintro ⟨hstruct, hhook⟩
          exact ⟨hconvert.mpr hstruct, hhook hgamma⟩)

/-- With positive gamma, the first-row-block basis predicate is uniform. -/
theorem firstRowBlockBasisPredicate_eq_uniform_of_gamma_pos
    (hgamma : 0 < D.gamma) (r n : ℕ) :
    D.FirstRowBlockBasisPredicate r n = Edrei.UniformBasisPredicate r n := by
  funext J
  apply propext
  rw [FirstRowBlockBasisPredicate, firstRowBlockMinor,
    D.toeplitzMinor_pos_iff_componentwise_le_of_gamma_pos hgamma]
  simp only [Edrei.UniformBasisPredicate, iff_true]
  exact firstNaturalRows_le_finiteSelectionNatural J

/-- In the zero-gamma branch, the first-row-block basis predicate is the Schubert hook
condition, conditional on the concrete finite-factor bridge. -/
theorem firstRowBlockBasisPredicate_eq_selectionHookCondition_of_gamma_zero
    (hgamma : D.gamma = 0) (hbridge : Edrei.GammaZeroTableauBridge D)
    (r n : ℕ) :
    D.FirstRowBlockBasisPredicate r n =
      (fun J : Fin r ↪o Fin n ↦ Edrei.SelectionHookCondition J p q) := by
  funext J
  apply propext
  rw [FirstRowBlockBasisPredicate, firstRowBlockMinor,
    D.toeplitzMinor_pos_iff_minorSupportCondition_of_gamma_zero hgamma hbridge]
  unfold MinorSupportCondition
  constructor
  · rintro ⟨_, hhook⟩
    exact (Edrei.indexHookInequalities_firstRowBlock_iff_selectionHookCondition J p q).mp
      (hhook hgamma)
  · intro hselection
    refine ⟨firstNaturalRows_le_finiteSelectionNatural J, ?_⟩
    intro _
    exact (Edrei.indexHookInequalities_firstRowBlock_iff_selectionHookCondition J p q).mpr
      hselection

end FiniteEdreiData

end

end ToeplitzPositroids
