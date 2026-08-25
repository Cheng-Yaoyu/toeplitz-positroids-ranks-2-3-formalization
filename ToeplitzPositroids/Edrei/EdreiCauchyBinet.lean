import ToeplitzPositroids.Edrei.ExponentialMinor
import ToeplitzPositroids.Matrix.CauchyBinet
import Mathlib.Tactic

/-!
# Cauchy--Binet for finite Edrei convolutions

This file realizes coefficient convolution as a product of sufficiently large finite Toeplitz
truncations.  Applying the rectangular Cauchy--Binet formula expresses every minor of the
convolution as a sum over intermediate increasing selections.  The final section specializes
this identity to the exponential and finite factors in finite Edrei data.
-/

namespace ToeplitzPositroids

open scoped BigOperators

noncomputable section

/-- Extend a sequence on the natural numbers by zero to negative integer indices. -/
def zeroExtendedNaturalSequence {R : Type*} [Zero R] (a : ℕ → R) (k : ℤ) : R :=
  if 0 ≤ k then a k.toNat else 0

@[simp]
theorem zeroExtendedNaturalSequence_ofNat {R : Type*} [Zero R] (a : ℕ → R) (n : ℕ) :
    zeroExtendedNaturalSequence a n = a n := by
  simp [zeroExtendedNaturalSequence]

theorem zeroExtendedNaturalSequence_eq_zero_of_neg {R : Type*} [Zero R]
    (a : ℕ → R) {k : ℤ} (hk : k < 0) :
    zeroExtendedNaturalSequence a k = 0 := by
  simp [zeroExtendedNaturalSequence, not_le.mpr hk]

/-- The ordinary Cauchy product of two sequences on the natural numbers. -/
def naturalConvolution {R : Type*} [Semiring R] (a b : ℕ → R) (n : ℕ) : R :=
  ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2

/-- A truncation through `N` contains every intermediate index contributing to the Toeplitz
entry from row `i` to column `j`, provided `j ≤ N`. -/
theorem zeroExtendedNaturalConvolution_eq_truncated_sum
    {R : Type*} [Semiring R] (a b : ℕ → R) (N i j : ℕ) (hjN : j ≤ N) :
    zeroExtendedNaturalSequence (naturalConvolution a b) ((j : ℤ) - (i : ℤ)) =
      ∑ k : Fin (N + 1),
        zeroExtendedNaturalSequence a ((k : ℤ) - (i : ℤ)) *
          zeroExtendedNaturalSequence b ((j : ℤ) - (k : ℤ)) := by
  by_cases hij : i ≤ j
  · have hnonneg : (0 : ℤ) ≤ (j : ℤ) - (i : ℤ) := by omega
    rw [zeroExtendedNaturalSequence, if_pos hnonneg, Int.toNat_sub]
    unfold naturalConvolution
    have hrestrict :
        (∑ k : Fin (N + 1),
            zeroExtendedNaturalSequence a ((k : ℤ) - (i : ℤ)) *
              zeroExtendedNaturalSequence b ((j : ℤ) - (k : ℤ))) =
          ∑ k : Fin (N + 1) with i ≤ k.val ∧ k.val ≤ j,
            zeroExtendedNaturalSequence a ((k : ℤ) - (i : ℤ)) *
              zeroExtendedNaturalSequence b ((j : ℤ) - (k : ℤ)) := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro k hk hkrange
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hkrange
      push Not at hkrange
      rcases lt_or_ge k.val i with hki | hik
      · rw [zeroExtendedNaturalSequence_eq_zero_of_neg a (by omega), zero_mul]
      · have hjk : j < k.val := hkrange hik
        rw [zeroExtendedNaturalSequence_eq_zero_of_neg b (by omega), mul_zero]
    rw [hrestrict]
    exact Finset.sum_bij
      (fun uv huv ↦ ⟨i + uv.1, by
        have huv' := Finset.mem_antidiagonal.mp huv
        omega⟩)
      (fun uv huv ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have huv' := Finset.mem_antidiagonal.mp huv
        omega)
      (fun u hu v hv huv ↦ by
        have huvVal := congrArg Fin.val huv
        change i + u.1 = i + v.1 at huvVal
        have hu' := Finset.mem_antidiagonal.mp hu
        have hv' := Finset.mem_antidiagonal.mp hv
        have hfirst : u.1 = v.1 := Nat.add_left_cancel huvVal
        exact Prod.ext hfirst (by omega))
      (fun k hk ↦ by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        refine ⟨(k.val - i, j - k.val), Finset.mem_antidiagonal.mpr (by omega), ?_⟩
        apply Fin.ext
        simp only
        omega)
      (fun uv huv ↦ by
        have huv' := Finset.mem_antidiagonal.mp huv
        simp only [zeroExtendedNaturalSequence, if_pos (show
          (0 : ℤ) ≤ (i + uv.1 : ℕ) - (i : ℤ) by omega),
          if_pos (show (0 : ℤ) ≤ (j : ℤ) - (i + uv.1 : ℕ) by omega)]
        rw [Int.toNat_sub, Int.toNat_sub]
        have hfirst : i + uv.1 - i = uv.1 := by omega
        have hsum : i + uv.1 + uv.2 = j := by omega
        have hsecond : j - (i + uv.1) = uv.2 := by omega
        rw [hfirst, hsecond])
  · have hneg : (j : ℤ) - (i : ℤ) < 0 := by omega
    rw [zeroExtendedNaturalSequence_eq_zero_of_neg _ hneg]
    symm
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hik : k.val < i
    · rw [zeroExtendedNaturalSequence_eq_zero_of_neg a (by omega), zero_mul]
    · rw [zeroExtendedNaturalSequence_eq_zero_of_neg b (by omega), mul_zero]

/-- The left rectangular Toeplitz truncation for a prescribed row selection. -/
def leftToeplitzTruncation {R : Type*} [Zero R] (a : ℕ → R) {r : ℕ}
    (rows : Fin r ↪o ℕ) (N : ℕ) : Matrix (Fin r) (Fin (N + 1)) R :=
  fun i k ↦ zeroExtendedNaturalSequence a ((k : ℤ) - (rows i : ℤ))

/-- The right rectangular Toeplitz truncation for a prescribed column selection. -/
def rightToeplitzTruncation {R : Type*} [Zero R] (b : ℕ → R) {r : ℕ}
    (cols : Fin r ↪o ℕ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin r) R :=
  fun k j ↦ zeroExtendedNaturalSequence b ((cols j : ℤ) - (k : ℤ))

@[simp]
theorem leftToeplitzTruncation_apply {R : Type*} [Zero R] (a : ℕ → R) {r : ℕ}
    (rows : Fin r ↪o ℕ) (N : ℕ) (i : Fin r) (k : Fin (N + 1)) :
    leftToeplitzTruncation a rows N i k =
      zeroExtendedNaturalSequence a ((k : ℤ) - (rows i : ℤ)) :=
  rfl

@[simp]
theorem rightToeplitzTruncation_apply {R : Type*} [Zero R] (b : ℕ → R) {r : ℕ}
    (cols : Fin r ↪o ℕ) (N : ℕ) (k : Fin (N + 1)) (j : Fin r) :
    rightToeplitzTruncation b cols N k j =
      zeroExtendedNaturalSequence b ((cols j : ℤ) - (k : ℤ)) :=
  rfl

/-- Regard an increasing selection in the finite truncation as a selection of natural indices. -/
def truncationSelection {r N : ℕ} (middle : Fin r ↪o Fin (N + 1)) : Fin r ↪o ℕ :=
  middle.trans (Fin.valOrderEmb (N + 1))

@[simp]
theorem truncationSelection_apply {r N : ℕ} (middle : Fin r ↪o Fin (N + 1))
    (i : Fin r) :
    truncationSelection middle i = middle i :=
  rfl

/-- Once the truncation reaches every selected column, multiplication of the two rectangular
Toeplitz sections is exactly the minor matrix of the coefficient convolution. -/
theorem leftToeplitzTruncation_mul_rightToeplitzTruncation
    {R : Type*} [CommSemiring R] (a b : ℕ → R) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    leftToeplitzTruncation a rows N * rightToeplitzTruncation b cols N =
      oneSidedToeplitzMinorMatrix
        (zeroExtendedNaturalSequence (naturalConvolution a b)) rows cols := by
  ext i j
  simp only [Matrix.mul_apply, leftToeplitzTruncation_apply,
    rightToeplitzTruncation_apply, oneSidedToeplitzMinorMatrix_apply]
  exact (zeroExtendedNaturalConvolution_eq_truncated_sum a b N (rows i) (cols j)
    (hcols j)).symm

/-- The minor of a one-sided coefficient convolution is a finite sum of products of minors.
The bound `N` is exact in the sense that it only has to contain the selected columns. -/
theorem oneSidedToeplitzMinor_naturalConvolution
    {R : Type*} [CommRing R] (a b : ℕ → R) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    oneSidedToeplitzMinor (zeroExtendedNaturalSequence (naturalConvolution a b)) rows cols =
      ∑ middle : Fin r ↪o Fin (N + 1),
        oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows
            (truncationSelection middle) *
          oneSidedToeplitzMinor (zeroExtendedNaturalSequence b)
            (truncationSelection middle) cols := by
  rw [oneSidedToeplitzMinor,
    ← leftToeplitzTruncation_mul_rightToeplitzTruncation a b rows cols hcols,
    Matrix.det_mul_eq_sum_orderedMinor]
  apply Finset.sum_congr rfl
  intro middle _
  simp [orderedMinor, allRows, oneSidedToeplitzMinor,
    leftToeplitzTruncation, rightToeplitzTruncation,
    truncationSelection, Matrix.submatrix]
  congr 1

/-- A natural-number selection whose values are at most `N`, bundled as a selection in the
finite truncation. -/
def boundedTruncationSelection {r N : ℕ} (cols : Fin r ↪o ℕ)
    (hcols : ∀ j, cols j ≤ N) : Fin r ↪o Fin (N + 1) :=
  OrderEmbedding.ofStrictMono
    (fun j ↦ ⟨cols j, Nat.lt_succ_of_le (hcols j)⟩)
    (fun _ _ hij ↦ cols.strictMono hij)

@[simp]
theorem boundedTruncationSelection_apply {r N : ℕ} (cols : Fin r ↪o ℕ)
    (hcols : ∀ j, cols j ≤ N) (i : Fin r) :
    (boundedTruncationSelection cols hcols i : ℕ) = cols i :=
  rfl

@[simp]
theorem truncationSelection_boundedTruncationSelection {r N : ℕ}
    (cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    truncationSelection (boundedTruncationSelection cols hcols) = cols := by
  apply DFunLike.ext _ _
  intro i
  rfl

/-- The principal minor of a zero-extended sequence with constant coefficient one is one. -/
@[simp]
theorem oneSidedToeplitzMinor_zeroExtended_principal
    {R : Type*} [CommRing R] (b : ℕ → R) (hb0 : b 0 = 1)
    {r : ℕ} (cols : Fin r ↪o ℕ) :
    oneSidedToeplitzMinor (zeroExtendedNaturalSequence b) cols cols = 1 := by
  apply oneSidedToeplitzMinor_principal
  · intro k hk
    exact zeroExtendedNaturalSequence_eq_zero_of_neg b hk
  · simpa using hb0

/-- The summand whose intermediate selection is the column selection is the first-factor minor;
the principal minor of the second factor contributes one. -/
theorem naturalConvolution_distinguished_summand
    (a b : ℕ → ℝ) (hb0 : b 0 = 1) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows
          (truncationSelection (boundedTruncationSelection cols hcols)) *
        oneSidedToeplitzMinor (zeroExtendedNaturalSequence b)
          (truncationSelection (boundedTruncationSelection cols hcols)) cols =
      oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows cols := by
  rw [truncationSelection_boundedTruncationSelection,
    oneSidedToeplitzMinor_zeroExtended_principal b hb0, mul_one]

/-- If every Cauchy--Binet summand is nonnegative, the distinguished summand gives a lower bound
for the minor of the convolution. -/
theorem oneSidedToeplitzMinor_le_naturalConvolution
    (a b : ℕ → ℝ) (hb0 : b 0 = 1) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N)
    (hsummand : ∀ middle : Fin r ↪o Fin (N + 1),
      0 ≤ oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows
            (truncationSelection middle) *
          oneSidedToeplitzMinor (zeroExtendedNaturalSequence b)
            (truncationSelection middle) cols) :
    oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows cols ≤
      oneSidedToeplitzMinor (zeroExtendedNaturalSequence (naturalConvolution a b)) rows cols := by
  rw [oneSidedToeplitzMinor_naturalConvolution a b rows cols hcols]
  have hterm := Finset.single_le_sum
    (fun middle (_ : middle ∈ (Finset.univ : Finset (Fin r ↪o Fin (N + 1)))) ↦
      hsummand middle)
    (Finset.mem_univ (boundedTruncationSelection cols hcols))
  rw [naturalConvolution_distinguished_summand a b hb0 rows cols hcols] at hterm
  exact hterm

/-- Positivity of the distinguished first-factor minor and nonnegativity of all summands imply
positivity of the convolution minor. -/
theorem oneSidedToeplitzMinor_naturalConvolution_pos
    (a b : ℕ → ℝ) (hb0 : b 0 = 1) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N)
    (hfirst : 0 < oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows cols)
    (hsummand : ∀ middle : Fin r ↪o Fin (N + 1),
      0 ≤ oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows
            (truncationSelection middle) *
          oneSidedToeplitzMinor (zeroExtendedNaturalSequence b)
            (truncationSelection middle) cols) :
    0 < oneSidedToeplitzMinor
      (zeroExtendedNaturalSequence (naturalConvolution a b)) rows cols :=
  hfirst.trans_le
    (oneSidedToeplitzMinor_le_naturalConvolution a b hb0 rows cols hcols hsummand)

/-- The largest value of a finite increasing natural-number selection.  For the empty
selection this is `0`. -/
def naturalSelectionBound {r : ℕ} (cols : Fin r ↪o ℕ) : ℕ :=
  Finset.univ.sup cols

/-- Every selected index lies below the canonical truncation bound. -/
theorem le_naturalSelectionBound {r : ℕ} (cols : Fin r ↪o ℕ) (j : Fin r) :
    cols j ≤ naturalSelectionBound cols :=
  Finset.le_sup (f := cols) (Finset.mem_univ j)

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- The finite alpha/beta factor, extended by zero to negative integer indices. -/
def finiteFactorSequence : ℤ → ℝ :=
  zeroExtendedNaturalSequence D.finiteFactorCoefficient

/-- A Toeplitz minor formed only from the finite alpha/beta factor.  This is deliberately
distinct from the older `finiteFactorMinor`, which uses the full data sequence and represents
the finite factor only after specializing `gamma` to zero. -/
def finiteFactorOnlyMinor {r : ℕ} (rows cols : Fin r ↪o ℕ) : ℝ :=
  oneSidedToeplitzMinor D.finiteFactorSequence rows cols

/-- The zeroth coefficient of the finite factor is one. -/
@[simp]
theorem finiteFactorCoefficient_zero : D.finiteFactorCoefficient 0 = 1 := by
  rw [finiteFactorCoefficient, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_finiteFactor]

/-- The Edrei coefficient sequence is the one-sided convolution of the exponential sequence
with the finite alpha/beta sequence. -/
theorem coefficient_eq_exponential_finite_convolution :
    D.coefficient =
      zeroExtendedNaturalSequence
        (naturalConvolution (fun n : ℕ ↦ exponentialCoefficient D.gamma n)
          D.finiteFactorCoefficient) := by
  funext k
  by_cases hk : 0 ≤ k
  · rw [FiniteEdreiData.coefficient, if_pos hk,
      zeroExtendedNaturalSequence, if_pos hk]
    simpa [naturalConvolution] using D.natCoefficient_eq_exponential_convolution k.toNat
  · rw [FiniteEdreiData.coefficient, if_neg hk,
      zeroExtendedNaturalSequence, if_neg hk]

/-- Zero-extending the natural exponential coefficients recovers the integer-indexed
exponential sequence. -/
theorem zeroExtended_exponentialCoefficient :
    zeroExtendedNaturalSequence (fun n : ℕ ↦ exponentialCoefficient D.gamma n) =
      exponentialCoefficient D.gamma := by
  funext k
  by_cases hk : 0 ≤ k
  · rw [zeroExtendedNaturalSequence, if_pos hk]
    have hkcast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk
    conv_rhs => rw [← hkcast]
  · have hkneg : k < 0 := lt_of_not_ge hk
    rw [zeroExtendedNaturalSequence, if_neg hk,
      exponentialCoefficient_eq_zero_of_neg D.gamma hkneg]

/-- The finite-factor sequence is one-sided. -/
theorem finiteFactorSequence_isOneSided : IsOneSidedSequence D.finiteFactorSequence := by
  intro k hk
  exact zeroExtendedNaturalSequence_eq_zero_of_neg D.finiteFactorCoefficient hk

/-- Every principal finite-factor-only minor is one. -/
@[simp]
theorem finiteFactorOnlyMinor_principal {r : ℕ} (cols : Fin r ↪o ℕ) :
    D.finiteFactorOnlyMinor cols cols = 1 := by
  exact oneSidedToeplitzMinor_zeroExtended_principal D.finiteFactorCoefficient
    D.finiteFactorCoefficient_zero cols

/-- Finite Cauchy--Binet formula for an Edrei Toeplitz minor. -/
theorem toeplitzMinor_eq_sum_exponential_finiteFactor {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    D.toeplitzMinor rows cols =
      ∑ middle : Fin r ↪o Fin (N + 1),
        exponentialToeplitzMinor D.gamma rows (truncationSelection middle) *
          D.finiteFactorOnlyMinor (truncationSelection middle) cols := by
  have hformula := oneSidedToeplitzMinor_naturalConvolution
    (fun n : ℕ ↦ exponentialCoefficient D.gamma n) D.finiteFactorCoefficient
    rows cols hcols
  rw [← D.coefficient_eq_exponential_finite_convolution,
    D.zeroExtended_exponentialCoefficient] at hformula
  simpa [FiniteEdreiData.toeplitzMinor, exponentialToeplitzMinor,
    finiteFactorOnlyMinor, finiteFactorSequence] using hformula

/-- Strict positivity of every structurally allowed exponential Toeplitz minor.  This is the
single exponential-kernel input needed by the Cauchy--Binet reduction. -/
def ExponentialAllowedMinorsPositive (gamma : ℝ) : Prop :=
  ∀ {r : ℕ} (rows cols : Fin r ↪o ℕ),
    (∀ i, rows i ≤ cols i) → 0 < exponentialToeplitzMinor gamma rows cols

/-- Total nonnegativity of the Toeplitz sequence formed by the finite alpha/beta factor. -/
def FiniteFactorMinorsNonnegative : Prop :=
  ∀ {r : ℕ} (rows cols : Fin r ↪o ℕ),
    0 ≤ D.finiteFactorOnlyMinor rows cols

/-- Every Cauchy--Binet summand is nonnegative under the two explicit factor hypotheses. -/
theorem exponential_finiteFactor_summand_nonneg
    (hexponential : ExponentialAllowedMinorsPositive D.gamma)
    (hfinite : D.FiniteFactorMinorsNonnegative) {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (middle : Fin r ↪o Fin (N + 1)) :
    0 ≤ exponentialToeplitzMinor D.gamma rows (truncationSelection middle) *
      D.finiteFactorOnlyMinor (truncationSelection middle) cols := by
  apply mul_nonneg
  · by_cases hallowed : ∀ i, rows i ≤ truncationSelection middle i
    · exact (hexponential rows (truncationSelection middle) hallowed).le
    · rw [exponentialToeplitzMinor_eq_zero_of_not_componentwise_le
        D.gamma rows (truncationSelection middle) hallowed]
  · exact hfinite (truncationSelection middle) cols

/-- The intermediate selection equal to `cols` contributes exactly the exponential minor. -/
theorem exponential_finiteFactor_distinguished_summand {r N : ℕ}
    (rows cols : Fin r ↪o ℕ) (hcols : ∀ j, cols j ≤ N) :
    exponentialToeplitzMinor D.gamma rows
          (truncationSelection (boundedTruncationSelection cols hcols)) *
        D.finiteFactorOnlyMinor
          (truncationSelection (boundedTruncationSelection cols hcols)) cols =
      exponentialToeplitzMinor D.gamma rows cols := by
  rw [truncationSelection_boundedTruncationSelection,
    D.finiteFactorOnlyMinor_principal, mul_one]

/-- Under factor nonnegativity, the exponential minor is a lower bound for the corresponding
minor of the full Edrei sequence. -/
theorem exponentialToeplitzMinor_le_toeplitzMinor
    (hexponential : ExponentialAllowedMinorsPositive D.gamma)
    (hfinite : D.FiniteFactorMinorsNonnegative) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) :
    exponentialToeplitzMinor D.gamma rows cols ≤ D.toeplitzMinor rows cols := by
  let N := naturalSelectionBound cols
  have hcols : ∀ j, cols j ≤ N := le_naturalSelectionBound cols
  rw [D.toeplitzMinor_eq_sum_exponential_finiteFactor rows cols hcols]
  have hterm := Finset.single_le_sum
    (fun middle (_ : middle ∈ (Finset.univ : Finset (Fin r ↪o Fin (N + 1)))) ↦
      D.exponential_finiteFactor_summand_nonneg hexponential hfinite rows cols middle)
    (Finset.mem_univ (boundedTruncationSelection cols hcols))
  rw [D.exponential_finiteFactor_distinguished_summand rows cols hcols] at hterm
  exact hterm

/-- Cauchy--Binet reduces positivity of an allowed Edrei minor to positivity of the corresponding
exponential minor, provided the finite factor is totally nonnegative. -/
theorem toeplitzMinor_pos_of_exponentialAllowedMinorsPositive
    (hexponential : ExponentialAllowedMinorsPositive D.gamma)
    (hfinite : D.FiniteFactorMinorsNonnegative) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    0 < D.toeplitzMinor rows cols :=
  (hexponential rows cols hallowed).trans_le
    (D.exponentialToeplitzMinor_le_toeplitzMinor hexponential hfinite rows cols)

/-- Exact support in the positive-exponential branch, conditional only on the two named factor
hypotheses.  Once general allowed exponential-minor positivity and finite-factor total
nonnegativity are supplied, this is the `gamma > 0` branch of the Edrei support theorem. -/
theorem toeplitzMinor_pos_iff_componentwise_le_of_factorHypotheses
    (hexponential : ExponentialAllowedMinorsPositive D.gamma)
    (hfinite : D.FiniteFactorMinorsNonnegative) {r : ℕ}
    (rows cols : Fin r ↪o ℕ) :
    0 < D.toeplitzMinor rows cols ↔ ∀ i, rows i ≤ cols i := by
  constructor
  · intro hpos
    by_contra hbad
    rw [D.toeplitzMinor_eq_zero_of_not_componentwise_le rows cols hbad] at hpos
    exact lt_irrefl 0 hpos
  · exact D.toeplitzMinor_pos_of_exponentialAllowedMinorsPositive
      hexponential hfinite rows cols

end FiniteEdreiData

end

end ToeplitzPositroids
