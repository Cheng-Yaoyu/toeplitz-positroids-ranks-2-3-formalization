import ToeplitzPositroids.RankThree.Banded
import ToeplitzPositroids.RankThree.SineSequence
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The consecutive-minor Jacobian

This file formalizes the fixed-endpoint consecutive-minor chart from Theorem 19.
The chart has `d - 1` variables and records the interior determinants
`D₁, ..., D_{d-1}`.  Its derivative is computed at the sine point and related to
the square of the tridiagonal recurrence matrix, including both endpoint
corrections when `d = 2`.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids Matrix
open scoped Matrix

noncomputable section

variable {d : ℕ}

/-- The abbreviations `s = sin θ` and `c = cos θ`. -/
def sineScale (d : ℕ) : ℝ := Real.sin (sineAngle d)

def cosineScale (d : ℕ) : ℝ := Real.cos (sineAngle d)

theorem sineScale_pos (d : ℕ) : 0 < sineScale d := by
  exact Real.sin_pos_of_pos_of_lt_pi (sineAngle_pos d) (sineAngle_lt_pi d)

/-- The sine sequence, extended by its trigonometric formula to integer indices. -/
def sineExtended (d : ℕ) (k : ℤ) : ℝ :=
  Real.sin (((k + 1 : ℤ) : ℝ) * sineAngle d)

@[simp]
theorem sineExtended_neg_one (d : ℕ) : sineExtended d (-1) = 0 := by
  simp [sineExtended]

@[simp]
theorem sineExtended_succ_last (d : ℕ) : sineExtended d (d + 1) = 0 := by
  rw [sineExtended]
  have hne : ((d + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : ((((d : ℤ) + 1 + 1 : ℤ) : ℝ) * sineAngle d) = Real.pi := by
    rw [sineAngle]
    push_cast
    field_simp
    ring
  rw [harg, Real.sin_pi]

/-- The elementary sine recurrence used at the base point. -/
theorem sin_add_eq_two_cos_mul_sin_sub (x θ : ℝ) :
    Real.sin (x + θ) = 2 * Real.cos θ * Real.sin x - Real.sin (x - θ) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- The constant log-concavity gap for three terms in an arithmetic sine progression. -/
theorem sin_sq_sub_mul_neighbors (x θ : ℝ) :
    Real.sin x ^ 2 - Real.sin (x - θ) * Real.sin (x + θ) = Real.sin θ ^ 2 := by
  rw [Real.sin_add, Real.sin_sub]
  nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq θ]

/-- Consecutive terms of the extended sine sequence satisfy the tridiagonal recurrence. -/
theorem sineExtended_recurrence (d : ℕ) (k : ℤ) :
    sineExtended d (k + 1) =
      2 * cosineScale d * sineExtended d k - sineExtended d (k - 1) := by
  let x := (((k + 1 : ℤ) : ℝ) * sineAngle d)
  have h := sin_add_eq_two_cos_mul_sin_sub x (sineAngle d)
  unfold sineExtended cosineScale
  convert h using 1
  all_goals dsimp only [x]
  all_goals congr 1
  all_goals push_cast
  all_goals ring_nf

/-- Every adjacent log-concavity gap of the extended sine sequence equals `s²`. -/
theorem sineExtended_logConcavity_gap (d : ℕ) (k : ℤ) :
    sineExtended d k ^ 2 - sineExtended d (k - 1) * sineExtended d (k + 1) =
      sineScale d ^ 2 := by
  let x := (((k + 1 : ℤ) : ℝ) * sineAngle d)
  have h := sin_sq_sub_mul_neighbors x (sineAngle d)
  unfold sineExtended sineScale
  convert h using 1
  all_goals dsimp only [x]
  all_goals congr 1
  all_goals push_cast
  all_goals ring_nf

/-- The five partial-derivative coefficients of `D_t` at the sine point. -/
theorem sineGradient_coefficients (d : ℕ) (t : ℤ) :
    sineExtended d (t + 1) ^ 2 - sineExtended d t * sineExtended d (t + 2) =
        sineScale d ^ 2 ∧
      -2 * sineExtended d t * sineExtended d (t + 1) +
          2 * sineExtended d (t - 1) * sineExtended d (t + 2) =
        -4 * cosineScale d * sineScale d ^ 2 ∧
      3 * sineExtended d t ^ 2 -
          2 * sineExtended d (t - 1) * sineExtended d (t + 1) -
          sineExtended d (t - 2) * sineExtended d (t + 2) =
        (4 * cosineScale d ^ 2 + 2) * sineScale d ^ 2 ∧
      -2 * sineExtended d (t - 1) * sineExtended d t +
          2 * sineExtended d (t - 2) * sineExtended d (t + 1) =
        -4 * cosineScale d * sineScale d ^ 2 ∧
      sineExtended d (t - 1) ^ 2 - sineExtended d (t - 2) * sineExtended d t =
        sineScale d ^ 2 := by
  let bm2 := sineExtended d (t - 2)
  let bm1 := sineExtended d (t - 1)
  let b0 := sineExtended d t
  let b1 := sineExtended d (t + 1)
  let b2 := sineExtended d (t + 2)
  let c := cosineScale d
  let s := sineScale d
  have hrecM : b0 = 2 * c * bm1 - bm2 := by
    dsimp only [b0, c, bm1, bm2]
    convert sineExtended_recurrence d (t - 1) using 1
    all_goals congr 1
    all_goals ring_nf
  have hrec0 : b1 = 2 * c * b0 - bm1 := by
    exact sineExtended_recurrence d t
  have hrecP : b2 = 2 * c * b1 - b0 := by
    dsimp only [b2, c, b1, b0]
    convert sineExtended_recurrence d (t + 1) using 1
    all_goals congr 1
    all_goals ring_nf
  have hbm2 : bm2 = 2 * c * bm1 - b0 := by linarith [hrecM]
  have hbm1 : bm1 = 2 * c * b0 - b1 := by linarith [hrec0]
  have hgapM : bm1 ^ 2 - bm2 * b0 = s ^ 2 := by
    dsimp only [bm1, bm2, b0, s]
    convert sineExtended_logConcavity_gap d (t - 1) using 1
    all_goals congr 1
    all_goals ring_nf
  have hgap0 : b0 ^ 2 - bm1 * b1 = s ^ 2 :=
    sineExtended_logConcavity_gap d t
  have hgapP : b1 ^ 2 - b0 * b2 = s ^ 2 := by
    dsimp only [b1, b0, b2, s]
    convert sineExtended_logConcavity_gap d (t + 1) using 1
    all_goals congr 1
    all_goals ring_nf
  change b1 ^ 2 - b0 * b2 = s ^ 2 ∧
    -2 * b0 * b1 + 2 * bm1 * b2 = -4 * c * s ^ 2 ∧
    3 * b0 ^ 2 - 2 * bm1 * b1 - bm2 * b2 = (4 * c ^ 2 + 2) * s ^ 2 ∧
    -2 * bm1 * b0 + 2 * bm2 * b1 = -4 * c * s ^ 2 ∧
    bm1 ^ 2 - bm2 * b0 = s ^ 2
  constructor
  · exact hgapP
  constructor
  · calc
      -2 * b0 * b1 + 2 * bm1 * b2 =
          -4 * c * (b0 ^ 2 - bm1 * b1) := by
              rw [hrecP, hbm1]
              ring
      _ = -4 * c * s ^ 2 := by rw [hgap0]
  constructor
  · calc
      3 * b0 ^ 2 - 2 * bm1 * b1 - bm2 * b2 =
          (4 * c ^ 2 + 2) * (b0 ^ 2 - bm1 * b1) := by
              rw [hbm2, hrecP, hbm1]
              ring
      _ = (4 * c ^ 2 + 2) * s ^ 2 := by rw [hgap0]
  constructor
  · calc
      -2 * bm1 * b0 + 2 * bm2 * b1 =
          -4 * c * (b0 ^ 2 - bm1 * b1) := by
              rw [hbm2, hrec0]
              ring
      _ = -4 * c * s ^ 2 := by rw [hgap0]
  · exact hgapM

/-- The interior part `(b₁,…,b_{d-1})` of the sine vector. -/
def sineInterior (d : ℕ) : Fin (d - 1) → ℝ :=
  fun i ↦ sineExtended d ((i.val : ℤ) + 1)

/-- The fixed-endpoint coefficient at any integer index.  Interior indices are
read from `x`; all other indices use the sine formula.  Only indices
`-1,…,d+1` occur in the chart, and the sine formula vanishes at `-1` and `d+1`. -/
def fixedEndpointCoefficient (d : ℕ) (x : Fin (d - 1) → ℝ) (k : ℤ) : ℝ :=
  if h : (1 : ℤ) ≤ k ∧ k ≤ d - 1 then
    x ⟨(k - 1).toNat, by omega⟩
  else
    sineExtended d k

/-- The derivative of one fixed-endpoint coefficient with respect to the
interior variables. -/
def fixedEndpointCoefficientCLM (d : ℕ) (k : ℤ) :
    (Fin (d - 1) → ℝ) →L[ℝ] ℝ :=
  if h : (1 : ℤ) ≤ k ∧ k ≤ d - 1 then
    ContinuousLinearMap.proj ⟨(k - 1).toNat, by omega⟩
  else
    0

theorem fixedEndpointCoefficientCLM_apply_of_mem {d : ℕ} {k : ℤ}
    (hk : (1 : ℤ) ≤ k ∧ k ≤ d - 1) (v : Fin (d - 1) → ℝ) :
    fixedEndpointCoefficientCLM d k v = v ⟨(k - 1).toNat, by omega⟩ := by
  unfold fixedEndpointCoefficientCLM
  rw [dif_pos hk]
  rfl

theorem fixedEndpointCoefficientCLM_apply_of_not_mem {d : ℕ} {k : ℤ}
    (hk : ¬((1 : ℤ) ≤ k ∧ k ≤ d - 1)) (v : Fin (d - 1) → ℝ) :
    fixedEndpointCoefficientCLM d k v = 0 := by
  unfold fixedEndpointCoefficientCLM
  rw [dif_neg hk]
  rfl

/-- Each fixed-endpoint coefficient is affine with the stated derivative. -/
theorem fixedEndpointCoefficient_hasStrictFDerivAt (d : ℕ)
    (x : Fin (d - 1) → ℝ) (k : ℤ) :
    HasStrictFDerivAt (fun y ↦ fixedEndpointCoefficient d y k)
      (fixedEndpointCoefficientCLM d k) x := by
  unfold fixedEndpointCoefficient fixedEndpointCoefficientCLM
  split_ifs with h
  · exact hasStrictFDerivAt_apply _ _
  · exact hasStrictFDerivAt_const _ _

/-- At the sine interior point, every chart coefficient is the corresponding
term of the extended sine sequence. -/
@[simp]
theorem fixedEndpointCoefficient_sineInterior (d : ℕ) (k : ℤ) :
    fixedEndpointCoefficient d (sineInterior d) k = sineExtended d k := by
  unfold fixedEndpointCoefficient
  split_ifs with h
  · unfold sineInterior
    congr 1
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ k - 1)]
    ring
  · rfl

/-- The five-term determinant polynomial at center index `t`. -/
def consecutivePolynomial (f : ℤ → ℝ) (t : ℤ) : ℝ :=
  f t ^ 3 - 2 * f (t - 1) * f t * f (t + 1) +
    f (t - 2) * f (t + 1) ^ 2 + f (t - 1) ^ 2 * f (t + 2) -
    f (t - 2) * f t * f (t + 2)

/-- The fixed-endpoint interior map `Φ`. -/
def consecutiveInteriorMap (d : ℕ) (x : Fin (d - 1) → ℝ) : Fin (d - 1) → ℝ :=
  fun i ↦ consecutivePolynomial (fixedEndpointCoefficient d x) ((i.val : ℤ) + 1)

/-- The gradient of the five-term determinant polynomial, expressed through
the five coefficient derivatives. -/
def consecutivePolynomialFDeriv (d : ℕ) (x : Fin (d - 1) → ℝ) (t : ℤ) :
    (Fin (d - 1) → ℝ) →L[ℝ] ℝ :=
  let bm2 := fixedEndpointCoefficient d x (t - 2)
  let bm1 := fixedEndpointCoefficient d x (t - 1)
  let b0 := fixedEndpointCoefficient d x t
  let b1 := fixedEndpointCoefficient d x (t + 1)
  let b2 := fixedEndpointCoefficient d x (t + 2)
  (b1 ^ 2 - b0 * b2) • fixedEndpointCoefficientCLM d (t - 2) +
    (-2 * b0 * b1 + 2 * bm1 * b2) • fixedEndpointCoefficientCLM d (t - 1) +
    (3 * b0 ^ 2 - 2 * bm1 * b1 - bm2 * b2) • fixedEndpointCoefficientCLM d t +
    (-2 * bm1 * b0 + 2 * bm2 * b1) • fixedEndpointCoefficientCLM d (t + 1) +
    (bm1 ^ 2 - bm2 * b0) • fixedEndpointCoefficientCLM d (t + 2)

/-- The assembled derivative of `Φ`. -/
def consecutiveInteriorFDeriv (d : ℕ) (x : Fin (d - 1) → ℝ) :
    (Fin (d - 1) → ℝ) →L[ℝ] (Fin (d - 1) → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ consecutivePolynomialFDeriv d x ((i.val : ℤ) + 1)

/-- The scalar five-term polynomial has the displayed strict derivative. -/
theorem consecutivePolynomial_hasStrictFDerivAt (d : ℕ)
    (x : Fin (d - 1) → ℝ) (t : ℤ) :
    HasStrictFDerivAt
      (fun y ↦ consecutivePolynomial (fixedEndpointCoefficient d y) t)
      (consecutivePolynomialFDeriv d x t) x := by
  let fm2 := fun y : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d y (t - 2)
  let fm1 := fun y : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d y (t - 1)
  let f0 := fun y : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d y t
  let f1 := fun y : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d y (t + 1)
  let f2 := fun y : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d y (t + 2)
  let Lm2 := fixedEndpointCoefficientCLM d (t - 2)
  let Lm1 := fixedEndpointCoefficientCLM d (t - 1)
  let L0 := fixedEndpointCoefficientCLM d t
  let L1 := fixedEndpointCoefficientCLM d (t + 1)
  let L2 := fixedEndpointCoefficientCLM d (t + 2)
  have hm2 : HasStrictFDerivAt fm2 Lm2 x :=
    fixedEndpointCoefficient_hasStrictFDerivAt d x (t - 2)
  have hm1 : HasStrictFDerivAt fm1 Lm1 x :=
    fixedEndpointCoefficient_hasStrictFDerivAt d x (t - 1)
  have h0 : HasStrictFDerivAt f0 L0 x :=
    fixedEndpointCoefficient_hasStrictFDerivAt d x t
  have h1 : HasStrictFDerivAt f1 L1 x :=
    fixedEndpointCoefficient_hasStrictFDerivAt d x (t + 1)
  have h2 : HasStrictFDerivAt f2 L2 x :=
    fixedEndpointCoefficient_hasStrictFDerivAt d x (t + 2)
  have hraw := ((((h0.pow 3).sub (((hm1.mul h0).mul h1).const_mul 2)).add
    (hm2.mul (h1.pow 2))).add ((hm1.pow 2).mul h2)).sub ((hm2.mul h0).mul h2)
  have h := hraw.congr_fderiv (by
    change _ = consecutivePolynomialFDeriv d x t
    ext v
    dsimp only [fm2, fm1, f0, f1, f2, Lm2, Lm1, L0, L1, L2]
    simp only [consecutivePolynomialFDeriv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring)
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y ↦ by
    simp only [consecutivePolynomial, fm2, fm1, f0, f1, f2, Pi.sub_apply,
      Pi.add_apply, Pi.mul_apply]
    ring

/-- The fixed-endpoint map `Φ` has the assembled strict Fréchet derivative. -/
theorem consecutiveInteriorMap_hasStrictFDerivAt (d : ℕ) (x : Fin (d - 1) → ℝ) :
    HasStrictFDerivAt (consecutiveInteriorMap d) (consecutiveInteriorFDeriv d x) x := by
  apply hasStrictFDerivAt_pi.mpr
  intro i
  exact consecutivePolynomial_hasStrictFDerivAt d x ((i.val : ℤ) + 1)

/-- The five-diagonal derivative row at the sine point. -/
def sineJacobianRow (d : ℕ) (t : ℤ) : (Fin (d - 1) → ℝ) →L[ℝ] ℝ :=
  sineScale d ^ 2 • fixedEndpointCoefficientCLM d (t - 2) +
    (-4 * cosineScale d * sineScale d ^ 2) • fixedEndpointCoefficientCLM d (t - 1) +
    ((4 * cosineScale d ^ 2 + 2) * sineScale d ^ 2) • fixedEndpointCoefficientCLM d t +
    (-4 * cosineScale d * sineScale d ^ 2) • fixedEndpointCoefficientCLM d (t + 1) +
    sineScale d ^ 2 • fixedEndpointCoefficientCLM d (t + 2)

/-- The full five-diagonal Jacobian at the sine point. -/
def sineJacobianCLM (d : ℕ) :
    (Fin (d - 1) → ℝ) →L[ℝ] (Fin (d - 1) → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ sineJacobianRow d ((i.val : ℤ) + 1)

@[simp]
theorem sineJacobianCLM_apply (d : ℕ) (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    sineJacobianCLM d v i = sineJacobianRow d ((i.val : ℤ) + 1) v :=
  rfl

/-- The symbolic derivative row reduces to the five constant stencil entries at
the sine point. -/
theorem consecutivePolynomialFDeriv_sineInterior (d : ℕ) (t : ℤ) :
    consecutivePolynomialFDeriv d (sineInterior d) t = sineJacobianRow d t := by
  rcases sineGradient_coefficients d t with ⟨hm2, hm1, h0, h1, h2⟩
  ext v
  simp only [consecutivePolynomialFDeriv, sineJacobianRow,
    fixedEndpointCoefficient_sineInterior, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hm2, hm1, h0, h1, h2]

/-- The derivative of `Φ` at the sine point is the five-diagonal sine Jacobian. -/
theorem consecutiveInteriorFDeriv_sineInterior (d : ℕ) :
    consecutiveInteriorFDeriv d (sineInterior d) = sineJacobianCLM d := by
  ext v i
  exact congrArg (fun L ↦ L v)
    (consecutivePolynomialFDeriv_sineInterior d ((i.val : ℤ) + 1))

/-- The fixed-endpoint map has the sine Jacobian as a strict derivative. -/
theorem consecutiveInteriorMap_hasStrictFDerivAt_sine (d : ℕ) :
    HasStrictFDerivAt (consecutiveInteriorMap d) (sineJacobianCLM d) (sineInterior d) := by
  exact (consecutiveInteriorMap_hasStrictFDerivAt d (sineInterior d)).congr_fderiv
    (consecutiveInteriorFDeriv_sineInterior d)

/-- The tridiagonal recurrence operator `T`. -/
def tridiagonalCLM (d : ℕ) :
    (Fin (d - 1) → ℝ) →L[ℝ] (Fin (d - 1) → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (2 * cosineScale d) • fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1) -
      fixedEndpointCoefficientCLM d (i.val : ℤ) -
        fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2)

@[simp]
theorem tridiagonalCLM_apply (d : ℕ) (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    tridiagonalCLM d v i =
      2 * cosineScale d * fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1) v -
        fixedEndpointCoefficientCLM d (i.val : ℤ) v -
          fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v := by
  rfl

/-- The first interior coordinate. -/
def firstInteriorIndex {d : ℕ} (hd : 2 ≤ d) : Fin (d - 1) := ⟨0, by omega⟩

/-- The last interior coordinate. -/
def lastInteriorIndex {d : ℕ} (hd : 2 ≤ d) : Fin (d - 1) := ⟨d - 2, by omega⟩

/-- The sum of the two endpoint rank-one terms.  When `d = 2`, both
conditions select the unique coordinate, so both contributions are retained. -/
def endpointCorrectionCLM {d : ℕ} (hd : 2 ≤ d) :
    (Fin (d - 1) → ℝ) →L[ℝ] (Fin (d - 1) → ℝ) :=
  ContinuousLinearMap.pi fun i ↦
    (if i = firstInteriorIndex hd then fixedEndpointCoefficientCLM d 1 else 0) +
      (if i = lastInteriorIndex hd then fixedEndpointCoefficientCLM d (d - 1) else 0)

@[simp]
theorem endpointCorrectionCLM_apply {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    endpointCorrectionCLM hd v i =
      (if i = firstInteriorIndex hd then fixedEndpointCoefficientCLM d 1 v else 0) +
        (if i = lastInteriorIndex hd then fixedEndpointCoefficientCLM d (d - 1) v else 0) := by
  unfold endpointCorrectionCLM
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.add_apply]
  split_ifs <;> rfl

/-- Coordinate form of the tridiagonal recurrence, with zero boundary values. -/
theorem tridiagonalCLM_apply_coordinates {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    tridiagonalCLM d v i = 2 * cosineScale d * v i -
      (if hi : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) -
      (if hi : i.val + 1 < d - 1 then v ⟨i.val + 1, hi⟩ else 0) := by
  have hcenter : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1) v = v i := by
    unfold fixedEndpointCoefficientCLM
    rw [dif_pos (by omega)]
    simp only [ContinuousLinearMap.proj_apply]
    congr 1
    apply Fin.ext
    simp
  by_cases hprev : 0 < i.val
  · have hleft : fixedEndpointCoefficientCLM d (i.val : ℤ) v =
        v ⟨i.val - 1, by omega⟩ := by
      unfold fixedEndpointCoefficientCLM
      rw [dif_pos (by omega)]
      simp only [ContinuousLinearMap.proj_apply]
      congr 1
      apply Fin.ext
      simp
    by_cases hnext : i.val + 1 < d - 1
    · have hh : ((i.val : ℤ) + 2).toNat = i.val + 2 := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ (i.val : ℤ) + 2)
      have hright : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v =
          v ⟨i.val + 1, hnext⟩ := by
        unfold fixedEndpointCoefficientCLM
        rw [dif_pos (by omega)]
        simp only [ContinuousLinearMap.proj_apply]
        apply congrArg v
        apply Fin.ext
        simp [hh]
      rw [tridiagonalCLM_apply, hcenter, hleft, hright, dif_pos hprev, dif_pos hnext]
    · have hright : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v = 0 := by
        unfold fixedEndpointCoefficientCLM
        rw [dif_neg (by omega)]
        rfl
      rw [tridiagonalCLM_apply, hcenter, hleft, hright, dif_pos hprev, dif_neg hnext]
  · have hleft : fixedEndpointCoefficientCLM d (i.val : ℤ) v = 0 := by
      unfold fixedEndpointCoefficientCLM
      rw [dif_neg (by omega)]
      rfl
    by_cases hnext : i.val + 1 < d - 1
    · have hh : ((i.val : ℤ) + 2).toNat = i.val + 2 := by
        exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ (i.val : ℤ) + 2)
      have hright : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v =
          v ⟨i.val + 1, hnext⟩ := by
        unfold fixedEndpointCoefficientCLM
        rw [dif_pos (by omega)]
        simp only [ContinuousLinearMap.proj_apply]
        apply congrArg v
        apply Fin.ext
        simp [hh]
      rw [tridiagonalCLM_apply, hcenter, hleft, hright, dif_neg hprev, dif_pos hnext]
    · have hright : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v = 0 := by
        unfold fixedEndpointCoefficientCLM
        rw [dif_neg (by omega)]
        rfl
      rw [tridiagonalCLM_apply, hcenter, hleft, hright, dif_neg hprev, dif_neg hnext]

/-- Direct kernel recurrence: a vector killed by `T` and vanishing at the first
coordinate vanishes identically. -/
theorem eq_zero_of_tridiagonalCLM_eq_zero_of_first_eq_zero {d : ℕ} (hd : 2 ≤ d)
    {v : Fin (d - 1) → ℝ} (hT : tridiagonalCLM d v = 0)
    (hfirst : v (firstInteriorIndex hd) = 0) :
    v = 0 := by
  have hz : ∀ (n : ℕ) (hn : n < d - 1), v ⟨n, hn⟩ = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn0 : n = 0
        · subst n
          simpa [firstInteriorIndex] using hfirst
        · let i : Fin (d - 1) := ⟨n - 1, by omega⟩
          have hcenter : v i = 0 := by
            apply ih (n - 1) (by omega) (by omega)
          have hprev : (if hi : 0 < i.val then v ⟨i.val - 1, by omega⟩ else 0) = 0 := by
            split_ifs with hi
            · apply ih (n - 2) (by omega) (by omega)
            · rfl
          have heq := congrFun hT i
          rw [tridiagonalCLM_apply_coordinates hd] at heq
          simp only [Pi.zero_apply] at heq
          have hnext : i.val + 1 < d - 1 := by simp [i]; omega
          rw [dif_pos hnext, hcenter, hprev] at heq
          have hindex : (⟨i.val + 1, hnext⟩ : Fin (d - 1)) = ⟨n, hn⟩ := by
            apply Fin.ext
            simp [i]
            omega
          rw [hindex] at heq
          linarith
  funext i
  simpa only [Pi.zero_apply] using hz i.val i.isLt

/-- Zero extension of an interior vector to integer indices. -/
def interiorExtension (d : ℕ) (v : Fin (d - 1) → ℝ) (k : ℤ) : ℝ :=
  if h : (0 : ℤ) ≤ k ∧ k < d - 1 then v ⟨k.toNat, by omega⟩ else 0

/-- A coefficient derivative is the corresponding zero-extended interior coordinate. -/
theorem fixedEndpointCoefficientCLM_apply_eq_interiorExtension (d : ℕ)
    (v : Fin (d - 1) → ℝ) (k : ℤ) :
    fixedEndpointCoefficientCLM d (k + 1) v = interiorExtension d v k := by
  unfold fixedEndpointCoefficientCLM interiorExtension
  split_ifs with h₁ h₂
  · simp only [ContinuousLinearMap.proj_apply]
    apply congrArg v
    apply Fin.ext
    norm_num
  · exfalso
    apply h₂
    omega
  · exfalso
    apply h₁
    omega
  · rfl

/-- Tridiagonal recurrence written entirely in zero-extended coordinates. -/
theorem tridiagonalCLM_apply_extension (d : ℕ) (v : Fin (d - 1) → ℝ)
    (i : Fin (d - 1)) :
    tridiagonalCLM d v i =
      2 * cosineScale d * interiorExtension d v i.val -
        interiorExtension d v (i.val - 1) - interiorExtension d v (i.val + 1) := by
  rw [tridiagonalCLM_apply]
  have hc := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v (i.val : ℤ)
  have hl : fixedEndpointCoefficientCLM d (i.val : ℤ) v =
      interiorExtension d v ((i.val : ℤ) - 1) := by
    calc
      _ = fixedEndpointCoefficientCLM d (((i.val : ℤ) - 1) + 1) v := by congr 1; ring_nf
      _ = _ := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) - 1)
  have hr : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 2) v =
      interiorExtension d v ((i.val : ℤ) + 1) := by
    calc
      _ = fixedEndpointCoefficientCLM d (((i.val : ℤ) + 1) + 1) v := by congr 1
      _ = _ := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) + 1)
  rw [hc, hl, hr]

/-- Extend `T v` and apply the same recurrence at every interior integer index. -/
theorem interiorExtension_tridiagonalCLM {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) (k : ℤ) :
    interiorExtension d (tridiagonalCLM d v) k =
      if (0 : ℤ) ≤ k ∧ k < d - 1 then
        2 * cosineScale d * interiorExtension d v k -
          interiorExtension d v (k - 1) - interiorExtension d v (k + 1)
      else 0 := by
  change (if hk : (0 : ℤ) ≤ k ∧ k < d - 1 then
      (tridiagonalCLM d v) ⟨k.toNat, by omega⟩ else 0) = _
  split_ifs with hk
  · let i : Fin (d - 1) := ⟨k.toNat, by omega⟩
    have hik : (i.val : ℤ) = k := by
      simp only [i]
      rw [Int.toNat_of_nonneg hk.1]
    change tridiagonalCLM d v i = _
    simpa only [hik] using tridiagonalCLM_apply_extension d v i
  · rfl

/-- The sine Jacobian row in zero-extended coordinate notation. -/
theorem sineJacobianCLM_apply_extension (d : ℕ) (v : Fin (d - 1) → ℝ)
    (i : Fin (d - 1)) :
    sineJacobianCLM d v i =
      sineScale d ^ 2 * interiorExtension d v (i.val - 2) -
        4 * cosineScale d * sineScale d ^ 2 * interiorExtension d v (i.val - 1) +
        (4 * cosineScale d ^ 2 + 2) * sineScale d ^ 2 * interiorExtension d v i.val -
        4 * cosineScale d * sineScale d ^ 2 * interiorExtension d v (i.val + 1) +
        sineScale d ^ 2 * interiorExtension d v (i.val + 2) := by
  rw [sineJacobianCLM_apply]
  unfold sineJacobianRow
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hm2 : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1 - 2) v =
      interiorExtension d v ((i.val : ℤ) - 2) := by
    calc
      _ = fixedEndpointCoefficientCLM d (((i.val : ℤ) - 2) + 1) v := by congr 1; ring_nf
      _ = _ := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) - 2)
  have hm1 : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1 - 1) v =
      interiorExtension d v ((i.val : ℤ) - 1) := by
    calc
      _ = fixedEndpointCoefficientCLM d (((i.val : ℤ) - 1) + 1) v := by congr 1; ring_nf
      _ = _ := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) - 1)
  have h0 := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v (i.val : ℤ)
  have h1 : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1 + 1) v =
      interiorExtension d v ((i.val : ℤ) + 1) := by
    exact fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) + 1)
  have h2 : fixedEndpointCoefficientCLM d ((i.val : ℤ) + 1 + 2) v =
      interiorExtension d v ((i.val : ℤ) + 2) := by
    calc
      _ = fixedEndpointCoefficientCLM d (((i.val : ℤ) + 2) + 1) v := by congr 1
      _ = _ := fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((i.val : ℤ) + 2)
  rw [hm2, hm1, h0, h1, h2]
  ring

private theorem interiorExtension_tridiagonalCLM_pred {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    interiorExtension d (tridiagonalCLM d v) ((i.val : ℤ) - 1) =
      2 * cosineScale d * interiorExtension d v ((i.val : ℤ) - 1) -
        interiorExtension d v ((i.val : ℤ) - 2) - interiorExtension d v i.val +
        (if i.val = 0 then interiorExtension d v 0 else 0) := by
  by_cases hi : i.val = 0
  · have hnot : ¬ ((0 : ℤ) ≤ (i.val : ℤ) - 1 ∧ (i.val : ℤ) - 1 < d - 1) := by
      omega
    rw [interiorExtension_tridiagonalCLM hd]
    simp only [hi, if_pos, Nat.cast_zero]
    simp [interiorExtension]
  · have hmem : (0 : ℤ) ≤ (i.val : ℤ) - 1 ∧ (i.val : ℤ) - 1 < d - 1 := by
      omega
    rw [interiorExtension_tridiagonalCLM hd]
    simp only [if_pos hmem, if_neg hi]
    ring_nf

private theorem interiorExtension_tridiagonalCLM_succ {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    interiorExtension d (tridiagonalCLM d v) ((i.val : ℤ) + 1) =
      2 * cosineScale d * interiorExtension d v ((i.val : ℤ) + 1) -
        interiorExtension d v i.val - interiorExtension d v ((i.val : ℤ) + 2) +
        (if i.val = d - 2 then interiorExtension d v (d - 2 : ℕ) else 0) := by
  by_cases hi : i.val = d - 2
  · have hnot : ¬ ((0 : ℤ) ≤ (i.val : ℤ) + 1 ∧ (i.val : ℤ) + 1 < d - 1) := by
      omega
    rw [interiorExtension_tridiagonalCLM hd]
    simp only [if_neg hnot, if_pos hi]
    have hzero_center : interiorExtension d v ((i.val : ℤ) + 1) = 0 := by
      unfold interiorExtension
      rw [dif_neg]
      omega
    have hzero_succ : interiorExtension d v ((i.val : ℤ) + 2) = 0 := by
      unfold interiorExtension
      rw [dif_neg]
      omega
    rw [hzero_center, hzero_succ]
    have hindex : ((i.val : ℤ) : ℤ) = (d - 2 : ℕ) := by omega
    rw [hindex]
    ring
  · have hmem : (0 : ℤ) ≤ (i.val : ℤ) + 1 ∧ (i.val : ℤ) + 1 < d - 1 := by
      omega
    rw [interiorExtension_tridiagonalCLM hd]
    simp only [if_pos hmem, if_neg hi]
    ring_nf

private theorem five_stencil_identity
    (s c xm2 xm1 x0 xp1 xp2 left right : ℝ) :
    s ^ 2 * xm2 - 4 * c * s ^ 2 * xm1 + (4 * c ^ 2 + 2) * s ^ 2 * x0 -
        4 * c * s ^ 2 * xp1 + s ^ 2 * xp2 =
      s ^ 2 *
        (2 * c * (2 * c * x0 - xm1 - xp1) -
          (2 * c * xm1 - xm2 - x0 + left) -
          (2 * c * xp1 - x0 - xp2 + right) + left + right) := by
  ring

/-- The actual sine Jacobian is `s²(T² + e₁e₁ᵀ + e_{d-1}e_{d-1}ᵀ)`.
The endpoint correction contains two summands even when `d = 2`. -/
theorem sineJacobianCLM_eq_tridiagonal_sq_add_endpoints {d : ℕ} (hd : 2 ≤ d) :
    sineJacobianCLM d = sineScale d ^ 2 •
      ((tridiagonalCLM d).comp (tridiagonalCLM d) + endpointCorrectionCLM hd) := by
  ext v i
  rw [sineJacobianCLM_apply_extension]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [tridiagonalCLM_apply_extension d (tridiagonalCLM d v) i]
  have hcenter :
      interiorExtension d (tridiagonalCLM d v) i.val =
        2 * cosineScale d * interiorExtension d v i.val -
          interiorExtension d v ((i.val : ℤ) - 1) -
          interiorExtension d v ((i.val : ℤ) + 1) := by
    rw [interiorExtension_tridiagonalCLM hd]
    rw [if_pos]
    constructor <;> omega
  rw [hcenter, interiorExtension_tridiagonalCLM_pred hd,
    interiorExtension_tridiagonalCLM_succ hd, endpointCorrectionCLM_apply]
  have hfirst : fixedEndpointCoefficientCLM d 1 v = interiorExtension d v 0 := by
    simpa using fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v 0
  have hlast : fixedEndpointCoefficientCLM d (d - 1) v =
      interiorExtension d v (d - 2 : ℕ) := by
    convert fixedEndpointCoefficientCLM_apply_eq_interiorExtension d v ((d : ℤ) - 2) using 1
    · congr 1
      ring_nf
    · congr 1
      omega
  rw [hfirst, hlast]
  have hfirstIndex : (i = firstInteriorIndex hd) ↔ i.val = 0 := by
    constructor
    · intro h
      subst i
      rfl
    · intro h
      apply Fin.ext
      simpa [firstInteriorIndex] using h
  have hlastIndex : (i = lastInteriorIndex hd) ↔ i.val = d - 2 := by
    constructor
    · intro h
      subst i
      rfl
    · intro h
      apply Fin.ext
      simpa [lastInteriorIndex] using h
  simp only [hfirstIndex, hlastIndex]
  simpa only [add_assoc] using five_stencil_identity
    (sineScale d) (cosineScale d)
    (interiorExtension d v ((i.val : ℤ) - 2))
    (interiorExtension d v ((i.val : ℤ) - 1))
    (interiorExtension d v i.val)
    (interiorExtension d v ((i.val : ℤ) + 1))
    (interiorExtension d v ((i.val : ℤ) + 2))
    (if i.val = 0 then interiorExtension d v 0 else 0)
    (if i.val = d - 2 then interiorExtension d v (d - 2 : ℕ) else 0)

/-- Reassemble the full band from its fixed endpoints and interior coordinates. -/
def fixedEndpointBand (d : ℕ) (x : Fin (d - 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun k ↦ fixedEndpointCoefficient d x k

/-- On every index used by an interior determinant, the band zero extension
agrees with the affine coefficient chart. -/
theorem bandCoefficient_fixedEndpointBand {d : ℕ} (x : Fin (d - 1) → ℝ)
    {k : ℤ} (hlo : -1 ≤ k) (hhi : k ≤ d + 1) :
    bandCoefficient (fixedEndpointBand d x) k = fixedEndpointCoefficient d x k := by
  by_cases hk : (0 : ℤ) ≤ k ∧ k ≤ d
  · rw [bandCoefficient]
    simp only [dif_pos hk, fixedEndpointBand]
    congr 1
    rw [Int.toNat_of_nonneg hk.1]
  · have hkcase : k = -1 ∨ k = d + 1 := by omega
    rcases hkcase with rfl | rfl
    · rw [bandCoefficient_neg_one]
      simp [fixedEndpointCoefficient]
    · rw [bandCoefficient_succ_last]
      unfold fixedEndpointCoefficient
      split_ifs
      · omega
      · exact (sineExtended_succ_last d).symm

/-- The polynomial chart really records the consecutive banded determinants
`D₁,…,D_{d-1}`. -/
theorem consecutiveInteriorMap_apply_eq_consecutiveDeterminant {d : ℕ} (hd : 2 ≤ d)
    (x : Fin (d - 1) → ℝ) (i : Fin (d - 1)) :
    consecutiveInteriorMap d x i =
      consecutiveDeterminant (fixedEndpointBand d x) ⟨i + 1, by omega⟩ := by
  rw [consecutiveDeterminant_polynomial]
  unfold consecutiveInteriorMap consecutivePolynomial
  push_cast
  have hm2 := bandCoefficient_fixedEndpointBand x
    (k := (i : ℤ) + 1 - 2) (by omega) (by omega)
  have hm1 := bandCoefficient_fixedEndpointBand x
    (k := (i : ℤ) + 1 - 1) (by omega) (by omega)
  have h0 := bandCoefficient_fixedEndpointBand x
    (k := (i : ℤ) + 1) (by omega) (by omega)
  have h1 := bandCoefficient_fixedEndpointBand x
    (k := (i : ℤ) + 1 + 1) (by omega) (by omega)
  have h2 := bandCoefficient_fixedEndpointBand x
    (k := (i : ℤ) + 1 + 2) (by omega) (by omega)
  rw [hm2, hm1, h0, h1, h2]

/-- The matrix of the actual strict derivative at the sine point. -/
def sineJacobianMatrix (d : ℕ) : Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ :=
  LinearMap.toMatrix' (sineJacobianCLM d).toLinearMap

/-- The tridiagonal matrix `T`. -/
def tridiagonalMatrix (d : ℕ) : Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ :=
  LinearMap.toMatrix' (tridiagonalCLM d).toLinearMap

/-- The two endpoint rank-one terms as a matrix. -/
def endpointCorrectionMatrix {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ :=
  LinearMap.toMatrix' (endpointCorrectionCLM hd).toLinearMap

/-- The matrix appearing on the right-hand side of Theorem 19. -/
def theoremNineteenMatrix {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℝ :=
  sineScale d ^ 2 •
    (tridiagonalMatrix d * tridiagonalMatrix d + endpointCorrectionMatrix hd)

theorem theoremNineteenMatrix_formula {d : ℕ} (hd : 2 ≤ d) :
    theoremNineteenMatrix hd = sineScale d ^ 2 •
      (tridiagonalMatrix d * tridiagonalMatrix d + endpointCorrectionMatrix hd) :=
  rfl

/-- Entry formula for the symmetric tridiagonal recurrence matrix. -/
theorem tridiagonalMatrix_apply {d : ℕ} (hd : 2 ≤ d)
    (i j : Fin (d - 1)) :
    tridiagonalMatrix d i j =
      if i = j then 2 * cosineScale d
      else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 := by
  simp only [tridiagonalMatrix, LinearMap.toMatrix'_apply]
  change tridiagonalCLM d (Pi.single j 1) i = _
  rw [tridiagonalCLM_apply_coordinates hd]
  simp only [Pi.single_apply]
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

/-- The tridiagonal recurrence matrix is Hermitian over the reals. -/
theorem tridiagonalMatrix_isHermitian {d : ℕ} (hd : 2 ≤ d) :
    (tridiagonalMatrix d).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  rw [tridiagonalMatrix_apply hd, tridiagonalMatrix_apply hd]
  simp only [star_trivial]
  by_cases hij : i = j
  · subst j
    simp
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    by_cases h : j.val + 1 = i.val ∨ i.val + 1 = j.val <;> simp_all [or_comm]

/-- The two endpoint evaluation rows used in the Gram factorization. -/
def endpointRows {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin 2) (Fin (d - 1)) ℝ :=
  fun r j ↦ if r = 0 then if j = firstInteriorIndex hd then 1 else 0
    else if j = lastInteriorIndex hd then 1 else 0

theorem fixedEndpointCoefficientCLM_one {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) :
    fixedEndpointCoefficientCLM d 1 v = v (firstInteriorIndex hd) := by
  rw [fixedEndpointCoefficientCLM_apply_of_mem (by omega)]
  congr 1

theorem fixedEndpointCoefficientCLM_last {d : ℕ} (hd : 2 ≤ d)
    (v : Fin (d - 1) → ℝ) :
    fixedEndpointCoefficientCLM d (d - 1) v = v (lastInteriorIndex hd) := by
  rw [fixedEndpointCoefficientCLM_apply_of_mem (by omega)]
  congr 1
  apply Fin.ext
  simp [lastInteriorIndex]
  omega

/-- The endpoint correction is the Gram matrix of the two endpoint rows. -/
theorem endpointCorrectionMatrix_eq_gram {d : ℕ} (hd : 2 ≤ d) :
    endpointCorrectionMatrix hd = (endpointRows hd).conjTranspose * endpointRows hd := by
  ext i j
  simp only [endpointCorrectionMatrix, LinearMap.toMatrix'_apply]
  change endpointCorrectionCLM hd (Pi.single j 1) i = _
  rw [endpointCorrectionCLM_apply]
  rw [fixedEndpointCoefficientCLM_one hd, fixedEndpointCoefficientCLM_last hd]
  simp only [conjTranspose_eq_transpose_of_trivial, mul_apply, transpose_apply, endpointRows,
    Fin.isValue, mul_ite, mul_one, mul_zero, Fin.sum_univ_two, ↓reduceIte, one_ne_zero]
  simp only [Pi.single_apply, Fin.ext_iff]
  have hfirst :
      (if i.val = (firstInteriorIndex hd).val then
          if (firstInteriorIndex hd).val = j.val then (1 : ℝ) else 0 else 0) =
        (if j.val = (firstInteriorIndex hd).val then
          if i.val = (firstInteriorIndex hd).val then 1 else 0 else 0) := by
    by_cases hi : i.val = (firstInteriorIndex hd).val
    · by_cases hj : j.val = (firstInteriorIndex hd).val
      · simp [hi, hj]
      · have hj' : (firstInteriorIndex hd).val ≠ j.val := Ne.symm hj
        simp [hi, hj, hj']
    · simp [hi]
  have hlast :
      (if i.val = (lastInteriorIndex hd).val then
          if (lastInteriorIndex hd).val = j.val then (1 : ℝ) else 0 else 0) =
        (if j.val = (lastInteriorIndex hd).val then
          if i.val = (lastInteriorIndex hd).val then 1 else 0 else 0) := by
    by_cases hi : i.val = (lastInteriorIndex hd).val
    · by_cases hj : j.val = (lastInteriorIndex hd).val
      · simp [hi, hj]
      · have hj' : (lastInteriorIndex hd).val ≠ j.val := Ne.symm hj
        simp [hi, hj, hj']
    · simp [hi]
  rw [hfirst, hlast]

/-- Stack the tridiagonal recurrence matrix and the two endpoint rows. -/
def augmentedMatrix {d : ℕ} (hd : 2 ≤ d) :
    Matrix (Fin (d - 1) ⊕ Fin 2) (Fin (d - 1)) ℝ :=
  Sum.elim (tridiagonalMatrix d) (endpointRows hd)

theorem augmentedMatrix_gram {d : ℕ} (hd : 2 ≤ d) :
    (augmentedMatrix hd).conjTranspose * augmentedMatrix hd =
      (tridiagonalMatrix d).conjTranspose * tridiagonalMatrix d +
        (endpointRows hd).conjTranspose * endpointRows hd := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    augmentedMatrix, Fintype.sum_sum_type, Matrix.add_apply]
  rfl

theorem endpointRows_mulVec_zero_first {d : ℕ} (hd : 2 ≤ d)
    {v : Fin (d - 1) → ℝ} (h : endpointRows hd *ᵥ v = 0) :
    v (firstInteriorIndex hd) = 0 := by
  have h0 := congrFun h (0 : Fin 2)
  classical
  simpa [endpointRows, Matrix.mulVec, dotProduct] using h0

/-- Injectivity of the augmented matrix follows directly from the recurrence
and the first endpoint value. -/
theorem augmentedMatrix_mulVec_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (augmentedMatrix hd).mulVec := by
  intro v w hvw
  suffices v - w = 0 by exact sub_eq_zero.mp this
  apply eq_zero_of_tridiagonalCLM_eq_zero_of_first_eq_zero hd
  · have hB : augmentedMatrix hd *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have hTM : tridiagonalMatrix d *ᵥ (v - w) = 0 := by
      funext i
      have hi := congrFun hB (Sum.inl i)
      change (∑ j, augmentedMatrix hd (Sum.inl i) j * (v - w) j) = 0 at hi
      change (∑ j, tridiagonalMatrix d i j * (v - w) j) = 0
      simpa [augmentedMatrix] using hi
    simpa only [tridiagonalMatrix, LinearMap.toMatrix'_mulVec] using hTM
  · have hB : augmentedMatrix hd *ᵥ (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    have hP : endpointRows hd *ᵥ (v - w) = 0 := by
      funext i
      have hi := congrFun hB (Sum.inr i)
      change (∑ j, augmentedMatrix hd (Sum.inr i) j * (v - w) j) = 0 at hi
      change (∑ j, endpointRows hd i j * (v - w) j) = 0
      simpa [augmentedMatrix] using hi
    exact endpointRows_mulVec_zero_first hd hP

/-- The matrix `T²` plus the two endpoint corrections is positive definite. -/
theorem coreMatrix_posDef {d : ℕ} (hd : 2 ≤ d) :
    (tridiagonalMatrix d * tridiagonalMatrix d + endpointCorrectionMatrix hd).PosDef := by
  have hgram := Matrix.PosDef.conjTranspose_mul_self (augmentedMatrix hd)
    (augmentedMatrix_mulVec_injective hd)
  rw [augmentedMatrix_gram] at hgram
  rw [(tridiagonalMatrix_isHermitian hd).eq] at hgram
  rw [endpointCorrectionMatrix_eq_gram]
  exact hgram

theorem coreCLM_toMatrix {d : ℕ} (hd : 2 ≤ d) :
    LinearMap.toMatrix'
        (((tridiagonalCLM d).comp (tridiagonalCLM d) + endpointCorrectionCLM hd).toLinearMap) =
      tridiagonalMatrix d * tridiagonalMatrix d + endpointCorrectionMatrix hd := by
  change LinearMap.toMatrix'
      ((tridiagonalCLM d).toLinearMap.comp (tridiagonalCLM d).toLinearMap +
        (endpointCorrectionCLM hd).toLinearMap) = _
  rw [map_add, LinearMap.toMatrix'_comp]
  rfl

/-- The positive-definite core of the Jacobian has trivial kernel. -/
theorem coreCLM_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective
      ((tridiagonalCLM d).comp (tridiagonalCLM d) + endpointCorrectionCLM hd) := by
  intro v w hvw
  let A := tridiagonalMatrix d * tridiagonalMatrix d + endpointCorrectionMatrix hd
  have hAvw : A *ᵥ v = A *ᵥ w := by
    dsimp only [A]
    rw [← coreCLM_toMatrix hd]
    simpa only [LinearMap.toMatrix'_mulVec] using hvw
  by_contra hvw_ne
  have hsub_ne : v - w ≠ 0 := sub_ne_zero.mpr hvw_ne
  have hpos := (coreMatrix_posDef hd).dotProduct_mulVec_pos hsub_ne
  have hzero : A *ᵥ (v - w) = 0 := by
    rw [Matrix.mulVec_sub, hAvw, sub_self]
  change 0 < star (v - w) ⬝ᵥ A *ᵥ (v - w) at hpos
  rw [hzero, dotProduct_zero] at hpos
  exact lt_irrefl 0 hpos

/-- The sine Jacobian is injective for every `d ≥ 2`. -/
theorem sineJacobianCLM_injective {d : ℕ} (hd : 2 ≤ d) :
    Function.Injective (sineJacobianCLM d) := by
  rw [sineJacobianCLM_eq_tridiagonal_sq_add_endpoints hd]
  intro v w hvw
  have hs_ne : sineScale d ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos (sineScale_pos d))
  apply coreCLM_injective hd
  funext i
  have hi := congrFun hvw i
  simp only [ContinuousLinearMap.smul_apply, Pi.smul_apply, smul_eq_mul] at hi
  exact mul_left_cancel₀ hs_ne hi

/-- Matrix form of the complete derivative identity in Theorem 19. -/
theorem sineJacobianMatrix_eq_theoremNineteenMatrix {d : ℕ} (hd : 2 ≤ d) :
    sineJacobianMatrix d = theoremNineteenMatrix hd := by
  unfold sineJacobianMatrix theoremNineteenMatrix
  rw [sineJacobianCLM_eq_tridiagonal_sq_add_endpoints hd]
  change LinearMap.toMatrix'
      (sineScale d ^ 2 •
        ((tridiagonalCLM d).toLinearMap.comp (tridiagonalCLM d).toLinearMap +
          (endpointCorrectionCLM hd).toLinearMap)) = _
  rw [map_smul, map_add, LinearMap.toMatrix'_comp]
  rfl

/-- The matrix in Theorem 19 is positive definite. -/
theorem theoremNineteenMatrix_posDef {d : ℕ} (hd : 2 ≤ d) :
    (theoremNineteenMatrix hd).PosDef := by
  unfold theoremNineteenMatrix
  exact (coreMatrix_posDef hd).smul (sq_pos_of_pos (sineScale_pos d))

/-- For `d = 2`, the two endpoint rank-one maps coincide and their contributions
are both present. -/
theorem endpointCorrectionCLM_two :
    endpointCorrectionCLM (d := 2) (by decide) =
      2 • ContinuousLinearMap.id ℝ (Fin 1 → ℝ) := by
  ext v i
  fin_cases i
  rw [endpointCorrectionCLM_apply]
  norm_num [firstInteriorIndex, lastInteriorIndex, fixedEndpointCoefficientCLM]
  ring

/-- The continuous-linear equivalence associated to the sine Jacobian. -/
noncomputable def sineJacobianContinuousLinearEquiv (d : ℕ) (hd : 2 ≤ d) :
    (Fin (d - 1) → ℝ) ≃L[ℝ] (Fin (d - 1) → ℝ) :=
  ContinuousLinearEquiv.ofBijective (sineJacobianCLM d)
    (LinearMap.ker_eq_bot.mpr (sineJacobianCLM_injective hd))
    (LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective (sineJacobianCLM_injective hd)))

/-- IFT-ready strict derivative statement bundled with an invertible derivative. -/
theorem consecutiveInteriorMap_hasStrictFDerivAt_equiv (d : ℕ) (hd : 2 ≤ d) :
    HasStrictFDerivAt (consecutiveInteriorMap d)
      (sineJacobianContinuousLinearEquiv d hd).toContinuousLinearMap
      (sineInterior d) := by
  simpa [sineJacobianContinuousLinearEquiv] using
    consecutiveInteriorMap_hasStrictFDerivAt_sine d

end

end ToeplitzPositroids.RankThree
