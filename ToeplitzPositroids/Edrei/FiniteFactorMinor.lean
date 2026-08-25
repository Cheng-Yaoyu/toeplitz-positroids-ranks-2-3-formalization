import ToeplitzPositroids.Edrei.IndexTuple
import ToeplitzPositroids.Edrei.PartitionHook
import ToeplitzPositroids.Edrei.PositiveExpansion
import ToeplitzPositroids.Edrei.ToeplitzMinor
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Finite-factor Edrei minors

This file develops the `gamma = 0` branch of Theorem 23.  All index arithmetic, structural zeros,
partition containment, hook inequalities, and the positive-sum support argument are formalized
here.  The abstract `FiniteFactorTableauExpansion` interface remains available for downstream
arguments; the concrete finite-factor LGV/tableau identity is discharged by the network/tableau
converse modules.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- Forget one-based indexing to obtain an increasing zero-based natural-number selection. -/
def IncreasingIndexTuple.zeroBasedOrderEmbedding {r : ℕ}
    (I : IncreasingIndexTuple r) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun k ↦ I k - 1) <| by
    intro i j hij
    have hstrict := I.strictMono hij
    have hi := I.position_le i
    have hj := I.position_le j
    change I i - 1 < I j - 1
    omega

@[simp]
theorem IncreasingIndexTuple.zeroBasedOrderEmbedding_apply {r : ℕ}
    (I : IncreasingIndexTuple r) (k : Fin r) :
    I.zeroBasedOrderEmbedding k = I k - 1 :=
  rfl

/-- The Toeplitz minor associated to one-based increasing row and column tuples. -/
def FiniteEdreiData.finiteFactorMinor {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) : ℝ :=
  D.toeplitzMinor I.zeroBasedOrderEmbedding J.zeroBasedOrderEmbedding

/-- At `gamma = 0`, the exponential factor is the constant series one. -/
theorem FiniteEdreiData.exponentialFactor_eq_one_of_gamma_eq_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) :
    D.exponentialFactor = 1 := by
  ext n
  cases n with
  | zero => simp [FiniteEdreiData.exponentialFactor, hgamma]
  | succ n => simp [FiniteEdreiData.exponentialFactor, hgamma]

/-- Thus the gamma-zero generating series is exactly the finite numerator product times the
finite inverse-denominator product. -/
theorem FiniteEdreiData.series_eq_betaProduct_mul_alphaProduct_of_gamma_eq_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) :
    D.series = D.betaProduct * D.alphaProduct := by
  rw [FiniteEdreiData.series,
    FiniteEdreiData.exponentialFactor_eq_one_of_gamma_eq_zero D hgamma, one_mul]

theorem FiniteEdreiData.natCoefficient_eq_finiteFactorCoefficient
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) (n : ℕ) :
    D.natCoefficient n = PowerSeries.coeff n (D.betaProduct * D.alphaProduct) := by
  rw [FiniteEdreiData.natCoefficient,
    FiniteEdreiData.series_eq_betaProduct_mul_alphaProduct_of_gamma_eq_zero D hgamma]

/-- Structural componentwise admissibility. -/
def StructurallyAdmissible {r : ℕ} (I J : IncreasingIndexTuple r) : Prop :=
  ∀ k, I k ≤ J k

/-- The original index form of the finite-factor hook inequalities
`j_{k-p} + p-q ≤ i_k`, written without truncated subtraction. -/
def IndexHookInequalities {r : ℕ} (I J : IncreasingIndexTuple r)
    (p q : ℕ) : Prop :=
  ∀ (k : Fin r), p < k.val + 1 →
    J ⟨k.val - p, by omega⟩ + p ≤ I k + q

/-- The partition-hook form `lambda_(t+p) ≤ mu_t+q`. -/
def PartitionHookInequalities {r : ℕ} (I J : IncreasingIndexTuple r)
    (p q : ℕ) : Prop :=
  ∀ t : ℕ, J.associatedPartZeroTail (t + p) ≤
    I.associatedPartZeroTail t + q

/-- Existence of the intermediate partition in the positive supersymmetric expansion. -/
def HasIntermediateStripPartition {r : ℕ} (I J : IncreasingIndexTuple r)
    (p q : ℕ) : Prop :=
  ∃ nu : ℕ → ℕ,
    IsPartitionSequence nu ∧
    (∀ t, I.associatedPartZeroTail t ≤ nu t) ∧
    (∀ t, nu t ≤ J.associatedPartZeroTail t) ∧
    (∀ t, J.associatedPartZeroTail t - nu t ≤ q) ∧
    (∀ t, nu (t + p) ≤ I.associatedPartZeroTail t)

/-- Structural admissibility is exactly containment of the associated partitions. -/
theorem structurallyAdmissible_iff_partition_containment {r : ℕ}
    (I J : IncreasingIndexTuple r) :
    StructurallyAdmissible I J ↔
      ∀ t, I.associatedPartZeroTail t ≤ J.associatedPartZeroTail t := by
  simpa [StructurallyAdmissible] using
    (I.associatedPartZeroTail_forall_le_iff J).symm

/-- Under structural containment, the intermediate strip partition exists exactly under the
partition-hook inequalities. -/
theorem hasIntermediateStripPartition_iff_partitionHook {r : ℕ}
    (I J : IncreasingIndexTuple r) (p q : ℕ) (hstruct : StructurallyAdmissible I J) :
    HasIntermediateStripPartition I J p q ↔ PartitionHookInequalities I J p q := by
  exact exists_intermediatePartition_iff_hook
    I.associatedPartZeroTail_isPartitionSequence
    J.associatedPartZeroTail_isPartitionSequence
    ((structurallyAdmissible_iff_partition_containment I J).mp hstruct) p q

/-- The partition-hook inequalities translate exactly to the original one-based index
inequalities of Theorem 23. -/
theorem partitionHookInequalities_iff_indexHook {r : ℕ}
    (I J : IncreasingIndexTuple r) (p q : ℕ) :
    PartitionHookInequalities I J p q ↔ IndexHookInequalities I J p q := by
  constructor
  · intro hhook k hk
    let t : ℕ := r - 1 - k.val
    have ht : t < r := by
      dsimp only [t]
      omega
    have htp : t + p < r := by
      dsimp only [t]
      omega
    let tf : Fin r := ⟨t, ht⟩
    let uf : Fin r := ⟨t + p, htp⟩
    let kp : Fin r := ⟨k.val - p, by omega⟩
    have htrev : tf.rev = k := by
      apply Fin.ext
      simp [tf, t]
      omega
    have hurev : uf.rev = kp := by
      apply Fin.ext
      simp [uf, kp, t]
      omega
    have h := hhook t
    rw [J.associatedPartZeroTail_apply htp, I.associatedPartZeroTail_apply ht] at h
    unfold IncreasingIndexTuple.associatedPart at h
    rw [htrev, hurev] at h
    have hkp : kp.val + p = k.val := by
      simp only [kp]
      exact Nat.sub_add_cancel (by omega)
    have hJpos := J.position_le kp
    have hIpos := I.position_le k
    change J kp + p ≤ I k + q
    omega
  · intro hindex t
    by_cases htp : t + p < r
    · have ht : t < r := by omega
      let tf : Fin r := ⟨t, ht⟩
      let uf : Fin r := ⟨t + p, htp⟩
      let k : Fin r := tf.rev
      let kp : Fin r := uf.rev
      have hk : p < k.val + 1 := by
        simp [k, tf]
        omega
      have hkp : kp.val = k.val - p := by
        simp [kp, k, uf, tf]
        omega
      have h := hindex k hk
      have harg : (⟨k.val - p, by omega⟩ : Fin r) = kp := by
        apply Fin.ext
        exact hkp.symm
      rw [harg] at h
      rw [J.associatedPartZeroTail_apply htp, I.associatedPartZeroTail_apply ht]
      unfold IncreasingIndexTuple.associatedPart
      change J kp - (kp.val + 1) ≤ I k - (k.val + 1) + q
      have hJpos := J.position_le kp
      have hIpos := I.position_le k
      have hrel : kp.val + p = k.val := by omega
      omega
    · have hz : J.associatedPartZeroTail (t + p) = 0 := by
        simp [IncreasingIndexTuple.associatedPartZeroTail, htp]
      rw [hz]
      exact Nat.zero_le _

/-- Failure of structural admissibility forces the finite-factor minor to vanish. -/
theorem FiniteEdreiData.finiteFactorMinor_eq_zero_of_not_structural
    {p q r : ℕ} (D : FiniteEdreiData p q) (I J : IncreasingIndexTuple r)
    (hbad : ¬StructurallyAdmissible I J) :
    finiteFactorMinor D I J = 0 := by
  apply D.toeplitzMinor_eq_zero_of_not_componentwise_le
  intro h
  apply hbad
  intro k
  have hk := h k
  simp only [IncreasingIndexTuple.zeroBasedOrderEmbedding_apply] at hk
  have hi := I.position_le k
  have hj := J.position_le k
  omega

/-- The precise missing tableau/LGV bridge.  Its finite indexing type should be the disjoint union
of pairs of semistandard skew tableaux over all intermediate partitions `nu`; the weight is the
corresponding positive alpha/beta monomial. -/
structure FiniteFactorTableauExpansion {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) where
  gamma_eq_zero : D.gamma = 0
  expansion : StrictPositiveExpansion (FiniteEdreiData.finiteFactorMinor D I J)
    (StructurallyAdmissible I J ∧ HasIntermediateStripPartition I J p q)

/-- An abstract gamma-zero bridge, quantified over all minor sizes and index tuples. -/
def GammaZeroTableauBridge {p q : ℕ} (D : FiniteEdreiData p q) : Type 1 :=
  ∀ (r : ℕ) (I J : IncreasingIndexTuple r), FiniteFactorTableauExpansion D I J

/-- The expansion interface is already constructible for principal minors; this sanity check also
fixes the normalization of the tableau sum. -/
def FiniteEdreiData.principalFiniteFactorTableauExpansion
    {p q r : ℕ} (D : FiniteEdreiData p q) (I : IncreasingIndexTuple r)
    (hgamma : D.gamma = 0) : FiniteFactorTableauExpansion D I I where
  gamma_eq_zero := hgamma
  expansion :=
    { index := PUnit
      indexFintype := inferInstance
      weight := fun _ ↦ 1
      weight_pos := by intro; norm_num
      value_eq_sum := by
        simp [FiniteEdreiData.finiteFactorMinor, FiniteEdreiData.toeplitzMinor_principal]
      nonempty_iff := by
        constructor
        · intro _
          refine ⟨fun _ ↦ le_rfl, ?_⟩
          let mu := I.associatedPartZeroTail
          refine ⟨mu, I.associatedPartZeroTail_isPartitionSequence,
            fun _ ↦ le_rfl, fun _ ↦ le_rfl, ?_, ?_⟩
          · intro t
            dsimp only [mu]
            omega
          · intro t
            exact I.associatedPartZeroTail_isPartitionSequence (Nat.le_add_right t p)
        · exact fun _ ↦ ⟨PUnit.unit⟩ }

/-- Once the finite supersymmetric Jacobi--Trudi expansion is supplied, positivity is equivalent
to structural containment and the partition-hook inequalities. -/
theorem FiniteEdreiData.finiteFactorMinor_pos_iff_partitionHook_of_expansion
    {p q r : ℕ} (D : FiniteEdreiData p q) (I J : IncreasingIndexTuple r)
    (hexp : FiniteFactorTableauExpansion D I J) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ PartitionHookInequalities I J p q := by
  have hpos := hexp.expansion.pos_iff
  constructor
  · intro hminor
    obtain ⟨hstruct, hintermediate⟩ := hpos.mp hminor
    exact ⟨hstruct,
      (hasIntermediateStripPartition_iff_partitionHook I J p q hstruct).mp hintermediate⟩
  · rintro ⟨hstruct, hhook⟩
    apply hpos.mpr
    exact ⟨hstruct,
      (hasIntermediateStripPartition_iff_partitionHook I J p q hstruct).mpr hhook⟩

/-- Conditional support theorem in the original index-hook notation. -/
theorem FiniteEdreiData.finiteFactorMinor_pos_iff_indexHook_of_expansion
    {p q r : ℕ} (D : FiniteEdreiData p q) (I J : IncreasingIndexTuple r)
    (hexp : FiniteFactorTableauExpansion D I J) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q := by
  rw [FiniteEdreiData.finiteFactorMinor_pos_iff_partitionHook_of_expansion D I J hexp,
    partitionHookInequalities_iff_indexHook]

/-- The gamma-zero support theorem follows for all minors from the single tableau/LGV bridge. -/
theorem FiniteEdreiData.finiteFactorMinor_pos_iff_indexHook
    {p q : ℕ} (D : FiniteEdreiData p q) (hbridge : GammaZeroTableauBridge D)
    {r : ℕ} (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q :=
  FiniteEdreiData.finiteFactorMinor_pos_iff_indexHook_of_expansion D I J
    (hbridge r I J)

/-- Positivity alone already forces the structural inequalities, independently of the tableau
expansion. -/
theorem FiniteEdreiData.structurallyAdmissible_of_finiteFactorMinor_pos
    {p q r : ℕ} (D : FiniteEdreiData p q) (I J : IncreasingIndexTuple r)
    (hpos : 0 < FiniteEdreiData.finiteFactorMinor D I J) :
    StructurallyAdmissible I J := by
  by_contra hbad
  rw [FiniteEdreiData.finiteFactorMinor_eq_zero_of_not_structural D I J hbad] at hpos
  exact lt_irrefl 0 hpos

end

end ToeplitzPositroids.Edrei
