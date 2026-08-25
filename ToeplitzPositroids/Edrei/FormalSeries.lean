import ToeplitzPositroids.Matrix.Toeplitz
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

/-!
# Formal series from finite Edrei data

This file defines the finite-parameter Edrei generating series entirely inside
`PowerSeries ℝ`. No analytic convergence is used. Its coefficients are extended by zero to
negative integer indices and then used to form infinite and finite Toeplitz sections.
-/

namespace ToeplitzPositroids

open PowerSeries

noncomputable section

/-- Finite Edrei parameters with the sign conditions used in Section 10. -/
structure FiniteEdreiData (p q : ℕ) where
  /-- Denominator parameters. -/
  alpha : Fin p → ℝ
  /-- Numerator parameters. -/
  beta : Fin q → ℝ
  /-- Exponential parameter. -/
  gamma : ℝ
  alpha_pos : ∀ i, 0 < alpha i
  beta_pos : ∀ j, 0 < beta j
  gamma_nonneg : 0 ≤ gamma

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- Coefficientwise nonnegativity of a real formal power series. -/
def CoeffNonnegative (f : ℝ⟦X⟧) : Prop :=
  ∀ n, 0 ≤ PowerSeries.coeff n f

/-- Coefficientwise strict positivity of a real formal power series. -/
def CoeffPositive (f : ℝ⟦X⟧) : Prop :=
  ∀ n, 0 < PowerSeries.coeff n f

/-- The formal geometric series `1 + aX + a²X² + ...`. -/
def geometricSeries (a : ℝ) : ℝ⟦X⟧ :=
  PowerSeries.rescale a (PowerSeries.mk 1)

@[simp]
theorem coeff_geometricSeries (a : ℝ) (n : ℕ) :
    PowerSeries.coeff n (geometricSeries a) = a ^ n := by
  simp [geometricSeries, PowerSeries.coeff_rescale]

/-- The geometric series is the inverse of `1 - aX`. -/
theorem geometricSeries_eq_inv_one_sub (a : ℝ) :
    geometricSeries a = (1 - PowerSeries.C a * PowerSeries.X)⁻¹ := by
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (by simp)).2
  have hfactor :
      1 - PowerSeries.C a * PowerSeries.X =
        PowerSeries.rescale a (1 - PowerSeries.X : ℝ⟦X⟧) := by
    simp [PowerSeries.rescale_X]
  rw [hfactor, geometricSeries, ← map_mul, PowerSeries.mk_one_mul_one_sub_eq_one]
  simp

/-- One numerator factor `1 + bX`. -/
def betaFactor (b : ℝ) : ℝ⟦X⟧ :=
  1 + PowerSeries.C b * PowerSeries.X

/-- One inverse denominator factor `(1 - aX)⁻¹`. -/
def alphaFactor (a : ℝ) : ℝ⟦X⟧ :=
  (1 - PowerSeries.C a * PowerSeries.X)⁻¹

/-- The rescaled formal exponential `exp(gamma X)`. -/
def exponentialFactor : ℝ⟦X⟧ :=
  PowerSeries.rescale D.gamma (PowerSeries.exp ℝ)

/-- The finite product of numerator factors. -/
def betaProduct : ℝ⟦X⟧ :=
  ∏ j : Fin q, betaFactor (D.beta j)

/-- The finite product of inverse denominator factors. -/
def alphaProduct : ℝ⟦X⟧ :=
  ∏ i : Fin p, alphaFactor (D.alpha i)

/-- The formal Edrei generating series
`exp(gamma X) * ∏ (1 + beta_j X) * ∏ (1 - alpha_i X)⁻¹`. -/
def series : ℝ⟦X⟧ :=
  D.exponentialFactor * D.betaProduct * D.alphaProduct

/-- Coefficients at natural-number indices. -/
def natCoefficient (n : ℕ) : ℝ :=
  PowerSeries.coeff n D.series

/-- Coefficients extended by zero to negative integer indices. -/
def coefficient (k : ℤ) : ℝ :=
  if 0 ≤ k then D.natCoefficient k.toNat else 0

/-- The bi-infinite Toeplitz matrix associated with the zero-extended coefficient sequence. -/
def infiniteToeplitz : Matrix ℤ ℤ ℝ :=
  fun i j ↦ D.coefficient (j - i)

/-- The finite `r × n` Toeplitz section associated with the Edrei coefficient sequence. -/
def finiteToeplitzSection (r n : ℕ) : Matrix (Fin r) (Fin n) ℝ :=
  toeplitzMatrix r n D.coefficient

@[simp]
theorem infiniteToeplitz_apply (i j : ℤ) :
    D.infiniteToeplitz i j = D.coefficient (j - i) :=
  rfl

@[simp]
theorem finiteToeplitzSection_apply {r n : ℕ} (i : Fin r) (j : Fin n) :
    D.finiteToeplitzSection r n i j = D.coefficient (j - i) :=
  rfl

/-- Coefficientwise nonnegativity is preserved by multiplication. -/
theorem CoeffNonnegative.mul {f g : ℝ⟦X⟧}
    (hf : CoeffNonnegative f) (hg : CoeffNonnegative g) :
    CoeffNonnegative (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (hf x.1) (hg x.2)

/-- A positive-coefficient series remains coefficientwise positive after multiplication by a
nonnegative-coefficient series of constant term one. -/
theorem CoeffPositive.mul_of_nonnegative_constantCoeff_one {f g : ℝ⟦X⟧}
    (hf : CoeffPositive f) (hg : CoeffNonnegative g)
    (hg0 : PowerSeries.constantCoeff g = 1) :
    CoeffPositive (f * g) := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (hf x.1).le (hg x.2)
  · refine ⟨(n, 0), by simp, ?_⟩
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hg0, mul_one]
    exact hf n

/-- Finite products of coefficientwise nonnegative series remain coefficientwise nonnegative. -/
theorem coeffNonnegative_prod {ι : Type*} [Fintype ι]
    (f : ι → ℝ⟦X⟧) (hf : ∀ i, CoeffNonnegative (f i)) :
    CoeffNonnegative (∏ i, f i) := by
  classical
  exact Finset.prod_induction f CoeffNonnegative
    (fun _ _ ha hb ↦ ha.mul hb)
    (by
      intro n
      by_cases hn : n = 0 <;> simp [hn])
    (fun i _ ↦ hf i)

/-- The exponential factor has nonnegative coefficients when `gamma ≥ 0`. -/
theorem exponentialFactor_coeff_nonneg : CoeffNonnegative D.exponentialFactor := by
  intro n
  rw [exponentialFactor, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  apply mul_nonneg (pow_nonneg D.gamma_nonneg n)
  have hcoeff : 0 < algebraMap ℚ ℝ (1 / n.factorial) := by
    norm_num
    exact Nat.factorial_pos n
  exact hcoeff.le

/-- If `gamma > 0`, every coefficient of the exponential factor is positive. -/
theorem exponentialFactor_coeff_pos (hgamma : 0 < D.gamma) :
    CoeffPositive D.exponentialFactor := by
  intro n
  rw [exponentialFactor, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  apply mul_pos (pow_pos hgamma n)
  norm_num
  exact Nat.factorial_pos n

/-- A numerator factor has nonnegative coefficients when its parameter is nonnegative. -/
theorem betaFactor_coeff_nonneg {b : ℝ} (hb : 0 ≤ b) :
    CoeffNonnegative (betaFactor b) := by
  intro n
  cases n with
  | zero => simp [betaFactor]
  | succ n =>
      cases n with
      | zero => simpa [betaFactor] using hb
      | succ n => simp [betaFactor]

/-- An inverse denominator factor has coefficient `a^n`. -/
@[simp]
theorem coeff_alphaFactor (a : ℝ) (n : ℕ) :
    PowerSeries.coeff n (alphaFactor a) = a ^ n := by
  rw [alphaFactor, ← geometricSeries_eq_inv_one_sub, coeff_geometricSeries]

/-- An inverse denominator factor has nonnegative coefficients for `a ≥ 0`. -/
theorem alphaFactor_coeff_nonneg {a : ℝ} (ha : 0 ≤ a) :
    CoeffNonnegative (alphaFactor a) := by
  intro n
  rw [coeff_alphaFactor]
  positivity

/-- The finite numerator product has nonnegative coefficients. -/
theorem betaProduct_coeff_nonneg : CoeffNonnegative D.betaProduct := by
  apply coeffNonnegative_prod
  intro j
  exact betaFactor_coeff_nonneg (D.beta_pos j).le

/-- The finite inverse-denominator product has nonnegative coefficients. -/
theorem alphaProduct_coeff_nonneg : CoeffNonnegative D.alphaProduct := by
  apply coeffNonnegative_prod
  intro i
  exact alphaFactor_coeff_nonneg (D.alpha_pos i).le

/-- Every factor used in the Edrei series has constant term one. -/
@[simp]
theorem constantCoeff_exponentialFactor :
    PowerSeries.constantCoeff D.exponentialFactor = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [exponentialFactor, PowerSeries.coeff_rescale]

@[simp]
theorem constantCoeff_betaFactor (b : ℝ) :
    PowerSeries.constantCoeff (betaFactor b) = 1 := by
  simp [betaFactor]

@[simp]
theorem constantCoeff_alphaFactor (a : ℝ) :
    PowerSeries.constantCoeff (alphaFactor a) = 1 := by
  simp [alphaFactor]

@[simp]
theorem constantCoeff_betaProduct : PowerSeries.constantCoeff D.betaProduct = 1 := by
  simp [betaProduct]

@[simp]
theorem constantCoeff_alphaProduct : PowerSeries.constantCoeff D.alphaProduct = 1 := by
  simp [alphaProduct]

/-- The Edrei series has constant term one. -/
@[simp]
theorem constantCoeff_series : PowerSeries.constantCoeff D.series = 1 := by
  simp [series]

/-- The natural Edrei coefficients are nonnegative. -/
theorem natCoefficient_nonneg (n : ℕ) : 0 ≤ D.natCoefficient n := by
  exact D.exponentialFactor_coeff_nonneg.mul D.betaProduct_coeff_nonneg |>.mul
    D.alphaProduct_coeff_nonneg n

/-- The zero-extended Edrei coefficients are nonnegative at every integer index. -/
theorem coefficient_nonneg (k : ℤ) : 0 ≤ D.coefficient k := by
  rw [coefficient]
  split_ifs
  · exact D.natCoefficient_nonneg _
  · exact le_rfl

/-- Every entry of the infinite Toeplitz matrix is nonnegative. -/
theorem infiniteToeplitz_entry_nonneg (i j : ℤ) :
    0 ≤ D.infiniteToeplitz i j :=
  D.coefficient_nonneg (j - i)

/-- Every entry of every finite Toeplitz section is nonnegative. -/
theorem finiteToeplitzSection_entry_nonneg {r n : ℕ} (i : Fin r) (j : Fin n) :
    0 ≤ D.finiteToeplitzSection r n i j :=
  D.coefficient_nonneg (j - i)

/-- Negative coefficient indices vanish. -/
@[simp]
theorem coefficient_eq_zero_of_neg {k : ℤ} (hk : k < 0) : D.coefficient k = 0 := by
  simp [coefficient, not_le.mpr hk]

/-- Natural indices recover the corresponding power-series coefficients. -/
@[simp]
theorem coefficient_ofNat (n : ℕ) : D.coefficient n = D.natCoefficient n := by
  simp [coefficient, natCoefficient]

/-- The constant coefficient is one. -/
@[simp]
theorem natCoefficient_zero : D.natCoefficient 0 = 1 := by
  rw [natCoefficient, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_series]

/-- If `gamma > 0`, every natural Edrei coefficient is strictly positive. -/
theorem natCoefficient_pos (hgamma : 0 < D.gamma) (n : ℕ) :
    0 < D.natCoefficient n := by
  have hrestNonneg : CoeffNonnegative (D.betaProduct * D.alphaProduct) :=
    D.betaProduct_coeff_nonneg.mul D.alphaProduct_coeff_nonneg
  have hrestConst : PowerSeries.constantCoeff (D.betaProduct * D.alphaProduct) = 1 := by
    simp
  have hpos := (D.exponentialFactor_coeff_pos hgamma).mul_of_nonnegative_constantCoeff_one
    hrestNonneg hrestConst n
  simpa [natCoefficient, series, mul_assoc] using hpos

/-- If `gamma > 0`, the zero-extended coefficient is positive exactly at nonnegative indices. -/
theorem coefficient_pos_iff (hgamma : 0 < D.gamma) (k : ℤ) :
    0 < D.coefficient k ↔ 0 ≤ k := by
  constructor
  · intro hk
    by_contra hneg
    have : k < 0 := lt_of_not_ge hneg
    rw [D.coefficient_eq_zero_of_neg this] at hk
    exact lt_irrefl 0 hk
  · intro hk
    rw [coefficient, if_pos hk]
    exact D.natCoefficient_pos hgamma k.toNat

end FiniteEdreiData

end

end ToeplitzPositroids
