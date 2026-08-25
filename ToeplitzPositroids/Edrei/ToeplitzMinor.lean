import ToeplitzPositroids.Edrei.FormalSeries
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Minors of one-sided Toeplitz matrices

This file begins the formalization of Theorem 23. It proves the structural-zero direction for
an arbitrary one-sided coefficient sequence: an increasing Toeplitz minor vanishes whenever its
`k`-th row index exceeds its `k`-th column index. It also records the checked positive consequences
of `gamma > 0` that follow directly from the formal-series development.
-/

namespace ToeplitzPositroids

noncomputable section

variable {R : Type*}

/-- A coefficient sequence is one-sided when all negative-index coefficients vanish. -/
def IsOneSidedSequence [Zero R] (h : ℤ → R) : Prop :=
  ∀ ⦃k : ℤ⦄, k < 0 → h k = 0

/-- The square Toeplitz submatrix on increasingly enumerated natural row and column indices. -/
def oneSidedToeplitzMinorMatrix (h : ℤ → R) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) : Matrix (Fin r) (Fin r) R :=
  fun a b ↦ h ((cols b : ℤ) - (rows a : ℤ))

/-- The corresponding ordered Toeplitz minor. -/
def oneSidedToeplitzMinor [CommRing R] (h : ℤ → R) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) : R :=
  (oneSidedToeplitzMinorMatrix h rows cols).det

@[simp]
theorem oneSidedToeplitzMinorMatrix_apply (h : ℤ → R) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (a b : Fin r) :
    oneSidedToeplitzMinorMatrix h rows cols a b =
      h ((cols b : ℤ) - (rows a : ℤ)) :=
  rfl

/-- A permutation must send some element of the initial segment through `k` to an element at
least `k`. This is the finite pigeonhole step in the structural-zero proof. -/
theorem exists_le_and_le_perm_apply {r : ℕ} (σ : Equiv.Perm (Fin r)) (k : Fin r) :
    ∃ c : Fin r, c ≤ k ∧ k ≤ σ c := by
  by_contra hnone
  have hmap : ∀ c : Fin r, c ≤ k → σ c < k := by
    intro c hck
    exact lt_of_not_ge fun hkc ↦ hnone ⟨c, hck, hkc⟩
  have hsubset : (Finset.Iic k).image σ ⊆ Finset.Iio k := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨c, hck, rfl⟩ := hx
    exact Finset.mem_Iio.mpr (hmap c (Finset.mem_Iic.mp hck))
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_image_of_injective _ σ.injective, Fin.card_Iic, Fin.card_Iio] at hcard
  omega

/-- Structural-zero theorem: if `rows k > cols k` for some position `k`, every Leibniz term
contains a negative-index coefficient, so the Toeplitz minor vanishes. -/
theorem oneSidedToeplitzMinor_eq_zero_of_exists_row_gt [CommRing R]
    {h : ℤ → R} (hone : IsOneSidedSequence h) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (k : Fin r) (hk : cols k < rows k) :
    oneSidedToeplitzMinor h rows cols = 0 := by
  rw [oneSidedToeplitzMinor, Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  obtain ⟨c, hck, hkc⟩ := exists_le_and_le_perm_apply σ k
  have hcol : cols c ≤ cols k := cols.monotone hck
  have hrow : rows k ≤ rows (σ c) := rows.monotone hkc
  have hneg : (cols c : ℤ) - (rows (σ c) : ℤ) < 0 := by
    omega
  have hentry : oneSidedToeplitzMinorMatrix h rows cols (σ c) c = 0 :=
    hone hneg
  have hprod : ∏ i, oneSidedToeplitzMinorMatrix h rows cols (σ i) i = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ c) hentry
  rw [hprod, smul_zero]

/-- Equivalent structural statement using negated componentwise admissibility. -/
theorem oneSidedToeplitzMinor_eq_zero_of_not_componentwise_le [CommRing R]
    {h : ℤ → R} (hone : IsOneSidedSequence h) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hbad : ¬∀ k, rows k ≤ cols k) :
    oneSidedToeplitzMinor h rows cols = 0 := by
  simp only [not_forall, not_le] at hbad
  obtain ⟨k, hk⟩ := hbad
  exact oneSidedToeplitzMinor_eq_zero_of_exists_row_gt hone rows cols k hk

/-- A principal one-sided Toeplitz minor is upper triangular. -/
theorem oneSidedToeplitzMinorMatrix_principal_blockTriangular [CommRing R]
    {h : ℤ → R} (hone : IsOneSidedSequence h) {r : ℕ} (rows : Fin r ↪o ℕ) :
    (oneSidedToeplitzMinorMatrix h rows rows).BlockTriangular id := by
  intro i j hji
  apply hone
  have hrows : rows j < rows i := rows.strictMono hji
  omega

/-- If the zeroth coefficient is one, every principal one-sided Toeplitz minor is one. -/
theorem oneSidedToeplitzMinor_principal [CommRing R]
    {h : ℤ → R} (hone : IsOneSidedSequence h) (hzero : h 0 = 1)
    {r : ℕ} (rows : Fin r ↪o ℕ) :
    oneSidedToeplitzMinor h rows rows = 1 := by
  rw [oneSidedToeplitzMinor,
    Matrix.det_of_upperTriangular (oneSidedToeplitzMinorMatrix_principal_blockTriangular hone rows)]
  simp [oneSidedToeplitzMinorMatrix, hzero]

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- The ordered Toeplitz minor attached to finite Edrei data. -/
def toeplitzMinor {r : ℕ} (rows cols : Fin r ↪o ℕ) : ℝ :=
  oneSidedToeplitzMinor D.coefficient rows cols

/-- The finite minor matrix is literally a submatrix of the bi-infinite Edrei Toeplitz matrix. -/
theorem oneSidedToeplitzMinorMatrix_eq_infiniteToeplitz_submatrix {r : ℕ}
    (rows cols : Fin r ↪o ℕ) :
    oneSidedToeplitzMinorMatrix D.coefficient rows cols =
      D.infiniteToeplitz.submatrix (fun i ↦ (rows i : ℤ)) (fun j ↦ (cols j : ℤ)) := by
  rfl

/-- The zero-extended Edrei coefficient sequence is one-sided. -/
theorem coefficient_isOneSided : IsOneSidedSequence D.coefficient := by
  intro k hk
  exact D.coefficient_eq_zero_of_neg hk

/-- The structural direction of Theorem 23 for finite Edrei data. -/
theorem toeplitzMinor_eq_zero_of_exists_row_gt {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (k : Fin r) (hk : cols k < rows k) :
    D.toeplitzMinor rows cols = 0 :=
  oneSidedToeplitzMinor_eq_zero_of_exists_row_gt D.coefficient_isOneSided rows cols k hk

/-- Failure of componentwise admissibility forces an Edrei Toeplitz minor to vanish. -/
theorem toeplitzMinor_eq_zero_of_not_componentwise_le {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hbad : ¬∀ k, rows k ≤ cols k) :
    D.toeplitzMinor rows cols = 0 :=
  oneSidedToeplitzMinor_eq_zero_of_not_componentwise_le D.coefficient_isOneSided rows cols hbad

/-- Every principal Edrei Toeplitz minor equals one. -/
@[simp]
theorem toeplitzMinor_principal {r : ℕ} (rows : Fin r ↪o ℕ) :
    D.toeplitzMinor rows rows = 1 :=
  oneSidedToeplitzMinor_principal D.coefficient_isOneSided
    (by
      rw [FiniteEdreiData.coefficient, if_pos (by norm_num)]
      change D.natCoefficient 0 = 1
      exact D.natCoefficient_zero) rows

/-- Under `gamma > 0`, every structurally allowed minor of order one is strictly positive. -/
theorem toeplitzMinor_one_pos (hgamma : 0 < D.gamma)
    (rows cols : Fin 1 ↪o ℕ) (hallowed : rows 0 ≤ cols 0) :
    0 < D.toeplitzMinor rows cols := by
  rw [toeplitzMinor, oneSidedToeplitzMinor, Matrix.det_fin_one]
  change 0 < D.coefficient ((cols 0 : ℤ) - (rows 0 : ℤ))
  exact (D.coefficient_pos_iff hgamma _).2 (by omega)

/-- Under `gamma > 0`, entries on and above the diagonal of the infinite Toeplitz matrix are
strictly positive. -/
theorem infiniteToeplitz_pos_of_le (hgamma : 0 < D.gamma) {i j : ℤ} (hij : i ≤ j) :
    0 < D.infiniteToeplitz i j := by
  rw [D.infiniteToeplitz_apply]
  exact (D.coefficient_pos_iff hgamma _).2 (sub_nonneg.mpr hij)

end FiniteEdreiData

end

end ToeplitzPositroids
