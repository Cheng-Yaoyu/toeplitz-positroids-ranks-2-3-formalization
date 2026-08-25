import ToeplitzPositroids.Edrei.ToeplitzMinor
import Mathlib.Tactic

/-!
# Exponential Toeplitz minors

This file isolates the exponential specialization in Theorem 23. It removes the positive
parameter `gamma` from every minor by positive diagonal row and column scalings, reducing the
remaining strict-positivity problem to the reciprocal-factorial kernel. It also records the exact
coefficient convolution with the finite alpha/beta factor.
-/

namespace ToeplitzPositroids

noncomputable section

/-- The one-sided exponential sequence `gamma^k / k!`. -/
def exponentialCoefficient (gamma : ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k then gamma ^ k.toNat / k.toNat.factorial else 0

/-- The reciprocal-factorial specialization, obtained by setting `gamma = 1`. -/
def factorialKernelCoefficient (k : ℤ) : ℝ :=
  if 0 ≤ k then 1 / k.toNat.factorial else 0

@[simp]
theorem exponentialCoefficient_ofNat (gamma : ℝ) (k : ℕ) :
    exponentialCoefficient gamma k = gamma ^ k / k.factorial := by
  simp [exponentialCoefficient]

@[simp]
theorem factorialKernelCoefficient_ofNat (k : ℕ) :
    factorialKernelCoefficient k = 1 / k.factorial := by
  simp [factorialKernelCoefficient]

theorem exponentialCoefficient_eq_zero_of_neg (gamma : ℝ) {k : ℤ} (hk : k < 0) :
    exponentialCoefficient gamma k = 0 := by
  simp [exponentialCoefficient, not_le.mpr hk]

theorem factorialKernelCoefficient_eq_zero_of_neg {k : ℤ} (hk : k < 0) :
    factorialKernelCoefficient k = 0 := by
  simp [factorialKernelCoefficient, not_le.mpr hk]

/-- The exponential sequence is the coefficient sequence of the rescaled formal exponential. -/
theorem coeff_rescale_exp (gamma : ℝ) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.rescale gamma (PowerSeries.exp ℝ)) =
      exponentialCoefficient gamma k := by
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, exponentialCoefficient_ofNat]
  norm_num
  rw [div_eq_mul_inv]

/-- The square exponential Toeplitz minor. -/
def exponentialToeplitzMinor {r : ℕ} (gamma : ℝ)
    (rows cols : Fin r ↪o ℕ) : ℝ :=
  oneSidedToeplitzMinor (exponentialCoefficient gamma) rows cols

/-- The reciprocal-factorial Toeplitz minor. -/
def factorialKernelMinor {r : ℕ} (rows cols : Fin r ↪o ℕ) : ℝ :=
  oneSidedToeplitzMinor factorialKernelCoefficient rows cols

/-- Entrywise scaling identity for the exponential and reciprocal-factorial kernels. -/
theorem exponentialCoefficient_sub_eq_zpow_mul_factorialKernel_mul_zpow
    {gamma : ℝ} (hgamma : gamma ≠ 0) (i j : ℕ) :
    exponentialCoefficient gamma ((j : ℤ) - (i : ℤ)) =
      gamma ^ (-(i : ℤ)) * factorialKernelCoefficient ((j : ℤ) - (i : ℤ)) *
        gamma ^ (j : ℤ) := by
  by_cases hij : i ≤ j
  · have hnonneg : (0 : ℤ) ≤ (j : ℤ) - (i : ℤ) := by omega
    rw [exponentialCoefficient, factorialKernelCoefficient, if_pos hnonneg, if_pos hnonneg]
    have hpow : gamma ^ ((j : ℤ) - (i : ℤ)).toNat =
        gamma ^ ((j : ℤ) - (i : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [hpow]
    have hzpow : gamma ^ (-(i : ℤ)) * gamma ^ (j : ℤ) =
        gamma ^ ((j : ℤ) - (i : ℤ)) := by
      rw [← zpow_add₀ hgamma]
      congr 1
      ring
    rw [← hzpow]
    ring
  · have hneg : (j : ℤ) - (i : ℤ) < 0 := by omega
    rw [exponentialCoefficient_eq_zero_of_neg gamma hneg,
      factorialKernelCoefficient_eq_zero_of_neg hneg, mul_zero, zero_mul]

/-- The exponential minor matrix is obtained from the factorial-kernel matrix by positive
diagonal row and column scalings. -/
theorem exponentialMinorMatrix_eq_diagonal_mul_factorial_mul_diagonal
    {r : ℕ} {gamma : ℝ} (hgamma : gamma ≠ 0)
    (rows cols : Fin r ↪o ℕ) :
    oneSidedToeplitzMinorMatrix (exponentialCoefficient gamma) rows cols =
      Matrix.diagonal (fun i ↦ gamma ^ (-(rows i : ℤ))) *
        oneSidedToeplitzMinorMatrix factorialKernelCoefficient rows cols *
          Matrix.diagonal (fun j ↦ gamma ^ (cols j : ℤ)) := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact exponentialCoefficient_sub_eq_zpow_mul_factorialKernel_mul_zpow
    hgamma (rows i) (cols j)

/-- Exact determinant scaling formula for exponential Toeplitz minors. -/
theorem exponentialToeplitzMinor_eq_scalars_mul_factorialKernelMinor
    {r : ℕ} {gamma : ℝ} (hgamma : gamma ≠ 0)
    (rows cols : Fin r ↪o ℕ) :
    exponentialToeplitzMinor gamma rows cols =
      (∏ i, gamma ^ (-(rows i : ℤ))) * factorialKernelMinor rows cols *
        ∏ j, gamma ^ (cols j : ℤ) := by
  rw [exponentialToeplitzMinor, factorialKernelMinor, oneSidedToeplitzMinor,
    oneSidedToeplitzMinor, exponentialMinorMatrix_eq_diagonal_mul_factorial_mul_diagonal
      hgamma rows cols,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]

/-- For `gamma > 0`, strict positivity of an exponential minor is equivalent to strict
positivity of the corresponding reciprocal-factorial minor. -/
theorem exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos
    {r : ℕ} {gamma : ℝ} (hgamma : 0 < gamma)
    (rows cols : Fin r ↪o ℕ) :
    0 < exponentialToeplitzMinor gamma rows cols ↔
      0 < factorialKernelMinor rows cols := by
  rw [exponentialToeplitzMinor_eq_scalars_mul_factorialKernelMinor hgamma.ne' rows cols,
    mul_assoc]
  have hrow : 0 < ∏ i, gamma ^ (-(rows i : ℤ)) :=
    Finset.prod_pos fun i _ ↦ zpow_pos hgamma _
  have hcol : 0 < ∏ j, gamma ^ (cols j : ℤ) :=
    Finset.prod_pos fun j _ ↦ zpow_pos hgamma _
  rw [mul_pos_iff_of_pos_left hrow, mul_pos_iff_of_pos_right hcol]

/-- Structural failure forces an exponential minor to vanish. -/
theorem exponentialToeplitzMinor_eq_zero_of_not_componentwise_le
    {r : ℕ} (gamma : ℝ) (rows cols : Fin r ↪o ℕ)
    (hbad : ¬∀ k, rows k ≤ cols k) :
    exponentialToeplitzMinor gamma rows cols = 0 := by
  apply oneSidedToeplitzMinor_eq_zero_of_not_componentwise_le
    (h := exponentialCoefficient gamma)
  · intro k hk
    exact exponentialCoefficient_eq_zero_of_neg gamma hk
  · exact hbad

/-- Every principal exponential minor is one. -/
@[simp]
theorem exponentialToeplitzMinor_principal {r : ℕ} (gamma : ℝ)
    (rows : Fin r ↪o ℕ) :
    exponentialToeplitzMinor gamma rows rows = 1 := by
  apply oneSidedToeplitzMinor_principal
  · intro k hk
    exact exponentialCoefficient_eq_zero_of_neg gamma hk
  · simp [exponentialCoefficient]

/-- Structurally allowed minors whose selected row/column intervals are block-separated are
upper triangular and strictly positive in every order. -/
theorem exponentialToeplitzMinor_pos_of_blockSeparated
    {r : ℕ} {gamma : ℝ} (hgamma : 0 < gamma)
    (rows cols : Fin r ↪o ℕ) (hdiag : ∀ i, rows i ≤ cols i)
    (hsep : ∀ {i j : Fin r}, j < i → cols j < rows i) :
    0 < exponentialToeplitzMinor gamma rows cols := by
  rw [exponentialToeplitzMinor, oneSidedToeplitzMinor,
    Matrix.det_of_upperTriangular]
  · apply Finset.prod_pos
    intro i hi
    change 0 < exponentialCoefficient gamma ((cols i : ℤ) - (rows i : ℤ))
    have hnonneg : (0 : ℤ) ≤ (cols i : ℤ) - (rows i : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr (hdiag i))
    rw [exponentialCoefficient, if_pos hnonneg]
    positivity
  · intro i j hji
    change exponentialCoefficient gamma ((cols j : ℤ) - (rows i : ℤ)) = 0
    apply exponentialCoefficient_eq_zero_of_neg
    exact sub_neg.mpr (Int.ofNat_lt.mpr (hsep hji))

/-- Ascending factorials of positive length strictly increase with their starting point. -/
theorem ascFactorial_strictMono_start {d b s : ℕ} (hdb : d < b) (hs : 0 < s) :
    (d + 1).ascFactorial s < (b + 1).ascFactorial s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs.ne'
  induction t with
  | zero =>
      simp only [Nat.ascFactorial_succ, Nat.ascFactorial_zero, Nat.add_zero,
        Nat.mul_one]
      omega
  | succ t ih =>
      rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
      have hfactor : d + 1 + (t + 1) < b + 1 + (t + 1) := by omega
      calc
        (d + 1 + (t + 1)) * (d + 1).ascFactorial (t + 1) <
            (b + 1 + (t + 1)) * (d + 1).ascFactorial (t + 1) :=
          Nat.mul_lt_mul_of_pos_right hfactor (Nat.ascFactorial_pos d (t + 1))
        _ ≤ (b + 1 + (t + 1)) * (b + 1).ascFactorial (t + 1) :=
          Nat.mul_le_mul_left _ (ih (by omega)).le

/-- The factorial inequality underlying strict positivity of order-two reciprocal-factorial
minors. -/
theorem factorial_cross_product_lt {d b s : ℕ} (hdb : d < b) (hs : 0 < s) :
    (d + s).factorial * b.factorial < (b + s).factorial * d.factorial := by
  have hasc := ascFactorial_strictMono_start hdb hs
  calc
    (d + s).factorial * b.factorial =
        (d.factorial * (d + 1).ascFactorial s) * b.factorial := by
      rw [Nat.factorial_mul_ascFactorial]
    _ < (d.factorial * (b + 1).ascFactorial s) * b.factorial := by
      gcongr
    _ = (b.factorial * (b + 1).ascFactorial s) * d.factorial := by
      ac_rfl
    _ = (b + s).factorial * d.factorial := by
      rw [Nat.factorial_mul_ascFactorial]

/-- Every structurally allowed reciprocal-factorial minor of order two is strictly positive. -/
theorem factorialKernelMinor_two_pos (rows cols : Fin 2 ↪o ℕ)
    (hallowed : ∀ i, rows i ≤ cols i) :
    0 < factorialKernelMinor rows cols := by
  have hrows : rows 0 < rows 1 := rows.strictMono (by decide)
  have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
  rw [factorialKernelMinor, oneSidedToeplitzMinor, Matrix.det_fin_two]
  change 0 <
    factorialKernelCoefficient ((cols 0 : ℤ) - (rows 0 : ℤ)) *
      factorialKernelCoefficient ((cols 1 : ℤ) - (rows 1 : ℤ)) -
    factorialKernelCoefficient ((cols 1 : ℤ) - (rows 0 : ℤ)) *
      factorialKernelCoefficient ((cols 0 : ℤ) - (rows 1 : ℤ))
  by_cases htri : cols 0 < rows 1
  · have hzero :
        factorialKernelCoefficient ((cols 0 : ℤ) - (rows 1 : ℤ)) = 0 :=
      factorialKernelCoefficient_eq_zero_of_neg (by omega)
    have hn00 : (0 : ℤ) ≤ (cols 0 : ℤ) - (rows 0 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr (hallowed 0))
    have hn11 : (0 : ℤ) ≤ (cols 1 : ℤ) - (rows 1 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr (hallowed 1))
    rw [hzero, mul_zero, sub_zero]
    rw [factorialKernelCoefficient, if_pos hn00,
      factorialKernelCoefficient, if_pos hn11]
    positivity
  · have hr1c0 : rows 1 ≤ cols 0 := by omega
    have hn00 : (0 : ℤ) ≤ (cols 0 : ℤ) - (rows 0 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr (hallowed 0))
    have hn11 : (0 : ℤ) ≤ (cols 1 : ℤ) - (rows 1 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr (hallowed 1))
    have hn01 : (0 : ℤ) ≤ (cols 1 : ℤ) - (rows 0 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr ((hallowed 0).trans hcols.le))
    have hn10 : (0 : ℤ) ≤ (cols 0 : ℤ) - (rows 1 : ℤ) :=
      sub_nonneg.mpr (Int.ofNat_le.mpr hr1c0)
    rw [factorialKernelCoefficient, if_pos hn00,
      factorialKernelCoefficient, if_pos hn11,
      factorialKernelCoefficient, if_pos hn01,
      factorialKernelCoefficient, if_pos hn10]
    let d := cols 0 - rows 1
    let b := cols 1 - rows 1
    let s := rows 1 - rows 0
    have hdb : d < b := Nat.sub_lt_sub_right hr1c0 hcols
    have hs : 0 < s := Nat.sub_pos_of_lt hrows
    have ha : cols 0 - rows 0 = d + s := by simp [d, s]; omega
    have hc : cols 1 - rows 0 = b + s := by simp [b, s]; omega
    have hfact := factorial_cross_product_lt hdb hs
    have hcast :
        ((d + s).factorial * b.factorial : ℕ) <
          (b + s).factorial * d.factorial := hfact
    rw [Int.toNat_sub, Int.toNat_sub, Int.toNat_sub, Int.toNat_sub]
    rw [ha, hc]
    have hrecip :
        (1 : ℝ) / ((b + s).factorial * d.factorial) <
          1 / ((d + s).factorial * b.factorial) := by
      apply one_div_lt_one_div_of_lt
      · positivity
      · exact_mod_cast hcast
    field_simp at hrecip ⊢
    nlinarith

/-- Consequently, every structurally allowed exponential minor of order two is strictly
positive when `gamma > 0`. -/
theorem exponentialToeplitzMinor_two_pos {gamma : ℝ} (hgamma : 0 < gamma)
    (rows cols : Fin 2 ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    0 < exponentialToeplitzMinor gamma rows cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma rows cols).2
    (factorialKernelMinor_two_pos rows cols hallowed)

/-- The part of a finite Edrei series not involving `gamma`. -/
def FiniteEdreiData.finiteFactor {p q : ℕ} (D : FiniteEdreiData p q) : PowerSeries ℝ :=
  D.betaProduct * D.alphaProduct

/-- Coefficients of the finite alpha/beta factor. -/
def FiniteEdreiData.finiteFactorCoefficient {p q : ℕ}
    (D : FiniteEdreiData p q) (n : ℕ) : ℝ :=
  PowerSeries.coeff n D.finiteFactor

/-- The finite alpha/beta factor has nonnegative coefficients. -/
theorem FiniteEdreiData.finiteFactor_coeff_nonneg {p q : ℕ}
    (D : FiniteEdreiData p q) :
    FiniteEdreiData.CoeffNonnegative D.finiteFactor :=
  D.betaProduct_coeff_nonneg.mul D.alphaProduct_coeff_nonneg

/-- The finite alpha/beta factor has constant term one. -/
@[simp]
theorem FiniteEdreiData.constantCoeff_finiteFactor {p q : ℕ}
    (D : FiniteEdreiData p q) :
    PowerSeries.constantCoeff D.finiteFactor = 1 := by
  simp [FiniteEdreiData.finiteFactor]

/-- Exact coefficient convolution between the exponential and finite factors. -/
theorem FiniteEdreiData.natCoefficient_eq_exponential_convolution {p q : ℕ}
    (D : FiniteEdreiData p q) (n : ℕ) :
    D.natCoefficient n =
      ∑ ij ∈ Finset.antidiagonal n,
        exponentialCoefficient D.gamma ij.1 * D.finiteFactorCoefficient ij.2 := by
  rw [FiniteEdreiData.natCoefficient, FiniteEdreiData.series, mul_assoc]
  change PowerSeries.coeff n (D.exponentialFactor * D.finiteFactor) = _
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [FiniteEdreiData.exponentialFactor, coeff_rescale_exp]
  rfl

/-- The exponential summand alone gives a strict lower bound witness in every coefficient when
`gamma > 0`; this is the coefficient-level precursor of the Cauchy--Binet argument. -/
theorem FiniteEdreiData.exponential_convolution_term_pos {p q : ℕ}
    (D : FiniteEdreiData p q) (hgamma : 0 < D.gamma) (n : ℕ) :
    0 < exponentialCoefficient D.gamma n * D.finiteFactorCoefficient 0 := by
  have hexp : 0 < exponentialCoefficient D.gamma n := by
    rw [exponentialCoefficient_ofNat]
    positivity
  have hfinite : D.finiteFactorCoefficient 0 = 1 := by
    rw [FiniteEdreiData.finiteFactorCoefficient,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      FiniteEdreiData.constantCoeff_finiteFactor]
  rw [hfinite, mul_one]
  exact hexp

/-- The finite factor can only increase each coefficient relative to the exponential
specialization. -/
theorem FiniteEdreiData.exponentialCoefficient_le_natCoefficient {p q : ℕ}
    (D : FiniteEdreiData p q) (n : ℕ) :
    exponentialCoefficient D.gamma n ≤ D.natCoefficient n := by
  rw [D.natCoefficient_eq_exponential_convolution]
  have hsummand : ∀ ij ∈ Finset.antidiagonal n,
      0 ≤ exponentialCoefficient D.gamma ij.1 * D.finiteFactorCoefficient ij.2 := by
    intro ij hij
    apply mul_nonneg
    · rw [exponentialCoefficient_ofNat]
      exact div_nonneg (pow_nonneg D.gamma_nonneg _) (Nat.cast_nonneg _)
    · exact D.finiteFactor_coeff_nonneg ij.2
  have hterm := Finset.single_le_sum hsummand
    (show (n, 0) ∈ Finset.antidiagonal n by simp)
  have hfinite : D.finiteFactorCoefficient 0 = 1 := by
    rw [FiniteEdreiData.finiteFactorCoefficient,
      PowerSeries.coeff_zero_eq_constantCoeff_apply,
      FiniteEdreiData.constantCoeff_finiteFactor]
  simpa [hfinite] using hterm

end

end ToeplitzPositroids
