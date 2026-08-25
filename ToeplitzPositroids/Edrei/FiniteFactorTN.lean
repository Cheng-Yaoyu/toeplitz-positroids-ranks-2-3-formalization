import ToeplitzPositroids.Edrei.EdreiCauchyBinet
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic

/-!
# Total nonnegativity of the finite Edrei factor

This file proves that the Toeplitz sequence of the finite alpha/beta factor has nonnegative
minors.  The proof starts with upper-bidiagonal chips, builds geometric Toeplitz truncations from
adjacent chips, and then uses Cauchy--Binet to show that convolution preserves nonnegativity.
-/

namespace ToeplitzPositroids

open scoped BigOperators
open PowerSeries

noncomputable section

/-- Total nonnegativity of square finite matrices is closed under multiplication. -/
theorem TotallyNonnegative.mul_fin {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : TotallyNonnegative A) (hB : TotallyNonnegative B) :
    TotallyNonnegative (A * B) := by
  intro k rows cols
  rw [orderedMinor]
  rw [← Matrix.submatrix_mul_equiv A B rows (Equiv.refl (Fin n)) cols,
    Matrix.det_mul_eq_sum_orderedMinor]
  apply Finset.sum_nonneg
  intro middle hmiddle
  have hleft := hA k rows middle
  have hright := hB k middle cols
  simpa [orderedMinor, allRows, Matrix.submatrix] using mul_nonneg hleft hright

/-- A square matrix is supported in the diagonal and first superdiagonal. -/
def HasUpperBidiagonalSupport {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, A i j ≠ 0 → i.val ≤ j.val ∧ j.val ≤ i.val + 1

/-- A nonidentity permutation cannot contribute to a minor of an upper-bidiagonal matrix whose
rows and columns are increasingly selected. -/
theorem upperBidiagonal_permutation_product_eq_zero {n k : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hsupport : HasUpperBidiagonalSupport A)
    (rows cols : Fin k ↪o Fin n) (sigma : Equiv.Perm (Fin k)) (hsigma : sigma ≠ 1) :
    ∏ i, (A.submatrix rows cols) (sigma i) i = 0 := by
  by_contra hprod
  have hnotmono : ¬Monotone sigma := by
    intro hmono
    exact hsigma ((Equiv.Perm.monotone_iff sigma).mp hmono)
  simp only [Monotone] at hnotmono
  push Not at hnotmono
  obtain ⟨i, j, hij, hsigmaji⟩ := hnotmono
  have hij' : i < j := lt_of_le_of_ne hij fun h ↦ by
    subst j
    exact (lt_irrefl _ hsigmaji).elim
  have hsigma' : sigma j < sigma i := hsigmaji
  have hiEntry : A (rows (sigma i)) (cols i) ≠ 0 := by
    intro hi
    apply hprod
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hjEntry : A (rows (sigma j)) (cols j) ≠ 0 := by
    intro hj
    apply hprod
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  obtain ⟨hiLower, hiUpper⟩ := hsupport _ _ hiEntry
  obtain ⟨hjLower, hjUpper⟩ := hsupport _ _ hjEntry
  have hrows : rows (sigma j) < rows (sigma i) := rows.strictMono hsigma'
  have hcols : cols i < cols j := cols.strictMono hij'
  omega

/-- Entrywise nonnegative upper-bidiagonal matrices are totally nonnegative. -/
theorem totallyNonnegative_of_upperBidiagonal {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hentry : ∀ i j, 0 ≤ A i j)
    (hsupport : HasUpperBidiagonalSupport A) :
    TotallyNonnegative A := by
  intro k rows cols
  rw [orderedMinor, Matrix.det_apply']
  rw [Finset.sum_eq_single 1]
  · simpa [Matrix.submatrix_apply] using
      (Finset.prod_nonneg fun i hi ↦ hentry (rows i) (cols i))
  · intro sigma hsigmaMem hsigma
    rw [upperBidiagonal_permutation_product_eq_zero hsupport rows cols sigma hsigma,
      mul_zero]
  · simp

/-- Natural coefficients of the elementary factor `1 + b X`. -/
def betaNaturalCoefficient (b : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 else if n = 1 then b else 0

theorem betaNaturalCoefficient_nonneg {b : ℝ} (hb : 0 ≤ b) (n : ℕ) :
    0 ≤ betaNaturalCoefficient b n := by
  simp only [betaNaturalCoefficient]
  split_ifs <;> positivity

/-- A nonzero entry of the beta-factor Toeplitz matrix lies on its diagonal or first
superdiagonal. -/
theorem betaToeplitz_support {b : ℝ} {N : ℕ} (i j : Fin (N + 1))
    (hentry : zeroExtendedNaturalSequence (betaNaturalCoefficient b)
      ((j : ℤ) - (i : ℤ)) ≠ 0) :
    i.val ≤ j.val ∧ j.val ≤ i.val + 1 := by
  by_cases hij : i.val ≤ j.val
  · constructor
    · exact hij
    · by_contra hfar
      have hdiff : j.val - i.val ≠ 0 ∧ j.val - i.val ≠ 1 := by omega
      apply hentry
      rw [show (j : ℤ) - (i : ℤ) = (j.val - i.val : ℕ) by omega]
      simp [betaNaturalCoefficient, hdiff.1, hdiff.2]
  · have hneg : (j : ℤ) - (i : ℤ) < 0 := by omega
    exact (hentry (zeroExtendedNaturalSequence_eq_zero_of_neg _ hneg)).elim

/-- Every finite Toeplitz section of a beta factor is totally nonnegative. -/
theorem betaToeplitz_totallyNonnegative {b : ℝ} (hb : 0 ≤ b) (N : ℕ) :
    TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence (betaNaturalCoefficient b)
        ((j : ℤ) - (i : ℤ))) := by
  apply totallyNonnegative_of_upperBidiagonal
  · intro i j
    by_cases hij : i.val ≤ j.val
    · rw [show (j : ℤ) - (i : ℤ) = (j.val - i.val : ℕ) by omega]
      simp only [zeroExtendedNaturalSequence_ofNat]
      exact betaNaturalCoefficient_nonneg hb _
    · rw [zeroExtendedNaturalSequence_eq_zero_of_neg _ (by omega)]
  · intro i j
    exact betaToeplitz_support i j

/-- The adjacent positive transvection connecting wires `x` and `x+1`. -/
def adjacentChip (a : ℝ) (N : ℕ) (x : Fin N) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.transvection x.castSucc x.succ a

/-- An adjacent chip has nonnegative entries when its parameter is nonnegative. -/
theorem adjacentChip_entry_nonneg {a : ℝ} (ha : 0 ≤ a) (N : ℕ) (x : Fin N)
    (i j : Fin (N + 1)) :
    0 ≤ adjacentChip a N x i j := by
  simp only [adjacentChip, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  split_ifs <;> positivity

/-- An adjacent chip is supported on the diagonal and first superdiagonal. -/
theorem adjacentChip_support (a : ℝ) (N : ℕ) (x : Fin N) :
    HasUpperBidiagonalSupport (adjacentChip a N x) := by
  intro i j hentry
  by_cases hij : i = j
  · subst j
    omega
  · by_cases hx : x.castSucc = i ∧ x.succ = j
    · rcases hx with ⟨rfl, rfl⟩
      simp
    · exfalso
      apply hentry
      simp [adjacentChip, Matrix.transvection, hij, hx]

/-- Every adjacent chip with a nonnegative parameter is totally nonnegative. -/
theorem adjacentChip_totallyNonnegative {a : ℝ} (ha : 0 ≤ a) (N : ℕ) (x : Fin N) :
    TotallyNonnegative (adjacentChip a N x) :=
  totallyNonnegative_of_upperBidiagonal (adjacentChip_entry_nonneg ha N x)
    (adjacentChip_support a N x)

/-- The ordered product of the adjacent chips at positions `0, ..., k-1`. -/
def geometricChipPrefix (a : ℝ) (N : ℕ) : (k : ℕ) → k ≤ N →
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0, _ => 1
  | k + 1, hk =>
      geometricChipPrefix a N k (by omega) *
        adjacentChip a N ⟨k, by omega⟩

/-- Entry formula for a prefix of the adjacent-chip product. -/
theorem geometricChipPrefix_apply (a : ℝ) (N : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N) (i j : Fin (N + 1)),
      geometricChipPrefix a N k hk i j =
        if i = j then 1
        else if i.val < j.val ∧ j.val ≤ k then a ^ (j.val - i.val) else 0 := by
  intro k
  induction k with
  | zero =>
      intro hk i j
      rw [geometricChipPrefix]
      simp only [Matrix.one_apply]
      by_cases hij : i = j
      · simp [hij]
      · rw [if_neg hij, if_neg hij]
        rw [if_neg (by omega : ¬(i.val < j.val ∧ j.val ≤ 0))]
  | succ k ih =>
      intro hk i j
      rw [geometricChipPrefix]
      let x : Fin N := ⟨k, by omega⟩
      by_cases hj : j = x.succ
      · subst j
        change (geometricChipPrefix a N k _ *
          Matrix.transvection x.castSucc x.succ a) i x.succ = _
        rw [Matrix.mul_transvection_apply_same x.castSucc x.succ i a]
        rw [ih (by omega), ih (by omega)]
        simp only [x, Fin.succ_mk, Fin.castSucc_mk]
        by_cases hi : i.val = k + 1
        · have hieq : i = (⟨k + 1, by omega⟩ : Fin (N + 1)) := Fin.ext hi
          simp [hieq]
        · by_cases hik : i.val = k
          · have hieq : i = (⟨k, by omega⟩ : Fin (N + 1)) := Fin.ext hik
            simp [hieq]
          · by_cases hil : i.val < k
            · have hiklt : i.val < k + 1 := by omega
              have hineSucc : i ≠ (⟨k + 1, by omega⟩ : Fin (N + 1)) := by
                intro h
                exact hi (congrArg Fin.val h)
              have hine : i ≠ (⟨k, by omega⟩ : Fin (N + 1)) := by
                intro h
                exact hik (congrArg Fin.val h)
              have hpow : k + 1 - i.val = (k - i.val) + 1 := by omega
              simp only [if_neg hineSucc, if_neg hine]
              rw [hpow, pow_succ]
              simp [hil, hiklt, mul_comm]
            · have higt : k + 1 < i.val := by omega
              have hineSucc : i ≠ (⟨k + 1, by omega⟩ : Fin (N + 1)) := by
                intro h
                exact hi (congrArg Fin.val h)
              have hine : i ≠ (⟨k, by omega⟩ : Fin (N + 1)) := by
                intro h
                exact hik (congrArg Fin.val h)
              simp [hineSucc, hine, hil, show ¬i.val ≤ k by omega]
      · change (geometricChipPrefix a N k _ *
          Matrix.transvection x.castSucc x.succ a) i j = _ at *
        rw [Matrix.mul_transvection_apply_of_ne x.castSucc x.succ i j hj a]
        rw [ih (by omega)]
        by_cases hjk : j.val = k + 1
        · exfalso
          apply hj
          apply Fin.ext
          simpa using hjk
        · by_cases hij : i = j
          · simp [hij]
          · rw [if_neg hij, if_neg hij]
            by_cases hlt : i.val < j.val
            · by_cases hjle : j.val ≤ k
              · rw [if_pos ⟨hlt, hjle⟩, if_pos ⟨hlt, by omega⟩]
              · rw [if_neg (by tauto), if_neg (by
                  intro h
                  omega)]
            · simp [hlt]

/-- The complete adjacent-chip product. -/
def geometricChipTransfer (a : ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  geometricChipPrefix a N N le_rfl

/-- The complete chip product is the finite Toeplitz matrix of the geometric sequence. -/
theorem geometricChipTransfer_apply (a : ℝ) (N : ℕ) (i j : Fin (N + 1)) :
    geometricChipTransfer a N i j =
      zeroExtendedNaturalSequence (fun n : ℕ ↦ a ^ n) ((j : ℤ) - (i : ℤ)) := by
  rw [geometricChipTransfer, geometricChipPrefix_apply]
  by_cases hij : i = j
  · subst j
    simp [zeroExtendedNaturalSequence]
  · by_cases hlt : i.val < j.val
    · rw [if_neg hij, if_pos ⟨hlt, by omega⟩]
      rw [show (j : ℤ) - (i : ℤ) = (j.val - i.val : ℕ) by omega]
      simp
    · have hneg : (j : ℤ) - (i : ℤ) < 0 := by omega
      rw [if_neg hij, if_neg (by omega),
        zeroExtendedNaturalSequence_eq_zero_of_neg _ hneg]

/-- Every prefix of the adjacent-chip product is totally nonnegative. -/
theorem geometricChipPrefix_totallyNonnegative {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    ∀ (k : ℕ) (hk : k ≤ N), TotallyNonnegative (geometricChipPrefix a N k hk) := by
  intro k
  induction k with
  | zero =>
      intro hk
      apply totallyNonnegative_of_upperBidiagonal
      · intro i j
        rw [geometricChipPrefix]
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      · intro i j hentry
        have hij : i = j := by
          by_contra hne
          apply hentry
          simp [geometricChipPrefix, hne]
        subst j
        omega
  | succ k ih =>
      intro hk
      rw [geometricChipPrefix]
      exact (ih (by omega)).mul_fin
        (adjacentChip_totallyNonnegative ha N ⟨k, by omega⟩)

/-- Every finite Toeplitz section of a geometric factor is totally nonnegative. -/
theorem geometricToeplitz_totallyNonnegative {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence (fun n : ℕ ↦ a ^ n)
        ((j : ℤ) - (i : ℤ))) := by
  have hmatrix : geometricChipTransfer a N =
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence (fun n : ℕ ↦ a ^ n)
        ((j : ℤ) - (i : ℤ))) := by
    ext i j
    exact geometricChipTransfer_apply a N i j
  rw [← hmatrix]
  exact geometricChipPrefix_totallyNonnegative ha N N le_rfl

/-- Every ordered Toeplitz minor of a natural sequence is nonnegative. -/
def NaturalSequenceMinorsNonnegative (a : ℕ → ℝ) : Prop :=
  ∀ {r : ℕ} (rows cols : Fin r ↪o ℕ),
    0 ≤ oneSidedToeplitzMinor (zeroExtendedNaturalSequence a) rows cols

/-- Total nonnegativity of every square truncation implies nonnegativity of every selected
Toeplitz minor. -/
theorem naturalSequenceMinorsNonnegative_of_finiteSections (a : ℕ → ℝ)
    (hsections : ∀ N : ℕ, TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence a
        ((j : ℤ) - (i : ℤ)))) :
    NaturalSequenceMinorsNonnegative a := by
  intro r rows cols
  let N := max (naturalSelectionBound rows) (naturalSelectionBound cols)
  have hrows : ∀ i, rows i ≤ N := fun i ↦
    (le_naturalSelectionBound rows i).trans (Nat.le_max_left _ _)
  have hcols : ∀ j, cols j ≤ N := fun j ↦
    (le_naturalSelectionBound cols j).trans (Nat.le_max_right _ _)
  have hminor := hsections N r (boundedTruncationSelection rows hrows)
    (boundedTruncationSelection cols hcols)
  simpa [orderedMinor, oneSidedToeplitzMinor, oneSidedToeplitzMinorMatrix,
    boundedTruncationSelection, Matrix.submatrix] using hminor

/-- Nonnegativity of all one-sided Toeplitz minors is preserved by coefficient convolution. -/
theorem NaturalSequenceMinorsNonnegative.convolution {a b : ℕ → ℝ}
    (ha : NaturalSequenceMinorsNonnegative a)
    (hb : NaturalSequenceMinorsNonnegative b) :
    NaturalSequenceMinorsNonnegative (naturalConvolution a b) := by
  intro r rows cols
  let N := naturalSelectionBound cols
  have hcols : ∀ j, cols j ≤ N := le_naturalSelectionBound cols
  rw [oneSidedToeplitzMinor_naturalConvolution a b rows cols hcols]
  apply Finset.sum_nonneg
  intro middle hmiddle
  exact mul_nonneg (ha rows (truncationSelection middle))
    (hb (truncationSelection middle) cols)

/-- The beta-factor sequence has nonnegative Toeplitz minors. -/
theorem betaNaturalCoefficient_minorsNonnegative {b : ℝ} (hb : 0 ≤ b) :
    NaturalSequenceMinorsNonnegative (betaNaturalCoefficient b) :=
  naturalSequenceMinorsNonnegative_of_finiteSections _
    (betaToeplitz_totallyNonnegative hb)

/-- The geometric sequence has nonnegative Toeplitz minors. -/
theorem geometricNaturalCoefficient_minorsNonnegative {a : ℝ} (ha : 0 ≤ a) :
    NaturalSequenceMinorsNonnegative (fun n : ℕ ↦ a ^ n) :=
  naturalSequenceMinorsNonnegative_of_finiteSections _
    (geometricToeplitz_totallyNonnegative ha)

/-- Coefficients of `1 + bX` agree with the elementary beta sequence. -/
theorem coeff_betaFactor_eq_betaNaturalCoefficient (b : ℝ) (n : ℕ) :
    PowerSeries.coeff n (FiniteEdreiData.betaFactor b) = betaNaturalCoefficient b n := by
  cases n with
  | zero => simp [FiniteEdreiData.betaFactor, betaNaturalCoefficient]
  | succ n =>
      cases n with
      | zero => simp [FiniteEdreiData.betaFactor, betaNaturalCoefficient]
      | succ n => simp [FiniteEdreiData.betaFactor, betaNaturalCoefficient]

/-- Each beta power-series factor has a totally nonnegative Toeplitz coefficient sequence. -/
theorem betaFactor_minorsNonnegative {b : ℝ} (hb : 0 ≤ b) :
    NaturalSequenceMinorsNonnegative
      (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.betaFactor b)) := by
  intro r rows cols
  simpa only [coeff_betaFactor_eq_betaNaturalCoefficient] using
    (betaNaturalCoefficient_minorsNonnegative hb rows cols)

/-- Each alpha power-series factor has a totally nonnegative Toeplitz coefficient sequence. -/
theorem alphaFactor_minorsNonnegative {a : ℝ} (ha : 0 ≤ a) :
    NaturalSequenceMinorsNonnegative
      (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.alphaFactor a)) := by
  intro r rows cols
  simpa only [FiniteEdreiData.coeff_alphaFactor] using
    (geometricNaturalCoefficient_minorsNonnegative ha rows cols)

/-- Every finite Toeplitz section of a beta power-series factor is totally nonnegative. -/
theorem betaFactorToeplitz_totallyNonnegative {b : ℝ} (hb : 0 ≤ b) (N : ℕ) :
    TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.betaFactor b))
        ((j : ℤ) - (i : ℤ))) := by
  have hmatrix :
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.betaFactor b))
        ((j : ℤ) - (i : ℤ))) =
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (betaNaturalCoefficient b) ((j : ℤ) - (i : ℤ))) := by
    ext i j
    congr 2
    exact funext (coeff_betaFactor_eq_betaNaturalCoefficient b)
  rw [hmatrix]
  exact betaToeplitz_totallyNonnegative hb N

/-- Every finite Toeplitz section of an alpha power-series factor is totally nonnegative. -/
theorem alphaFactorToeplitz_totallyNonnegative {a : ℝ} (ha : 0 ≤ a) (N : ℕ) :
    TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.alphaFactor a))
        ((j : ℤ) - (i : ℤ))) := by
  have hmatrix :
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (fun n ↦ PowerSeries.coeff n (FiniteEdreiData.alphaFactor a))
        ((j : ℤ) - (i : ℤ))) =
      (fun i j : Fin (N + 1) ↦ zeroExtendedNaturalSequence
        (fun n : ℕ ↦ a ^ n) ((j : ℤ) - (i : ℤ))) := by
    ext i j
    congr 2
    exact funext (FiniteEdreiData.coeff_alphaFactor a)
  rw [hmatrix]
  exact geometricToeplitz_totallyNonnegative ha N

/-- The property that the coefficient sequence of a power series has nonnegative Toeplitz
minors. -/
def PowerSeriesMinorsNonnegative (f : ℝ⟦X⟧) : Prop :=
  NaturalSequenceMinorsNonnegative (fun n ↦ PowerSeries.coeff n f)

/-- Multiplication of power series preserves nonnegativity of all coefficient Toeplitz minors. -/
theorem PowerSeriesMinorsNonnegative.mul {f g : ℝ⟦X⟧}
    (hf : PowerSeriesMinorsNonnegative f) (hg : PowerSeriesMinorsNonnegative g) :
    PowerSeriesMinorsNonnegative (f * g) := by
  have hcoeff : (fun n ↦ PowerSeries.coeff n (f * g)) =
      naturalConvolution (fun n ↦ PowerSeries.coeff n f)
        (fun n ↦ PowerSeries.coeff n g) := by
    funext n
    rw [PowerSeries.coeff_mul]
    rfl
  rw [PowerSeriesMinorsNonnegative, hcoeff]
  exact hf.convolution hg

/-- The constant power series one has a totally nonnegative Toeplitz coefficient sequence. -/
theorem powerSeriesOne_minorsNonnegative :
    PowerSeriesMinorsNonnegative (1 : ℝ⟦X⟧) := by
  have hcoeff : (fun n : ℕ ↦ PowerSeries.coeff n (1 : ℝ⟦X⟧)) =
      betaNaturalCoefficient 0 := by
    funext n
    rw [← coeff_betaFactor_eq_betaNaturalCoefficient 0 n]
    simp [FiniteEdreiData.betaFactor]
  rw [PowerSeriesMinorsNonnegative, NaturalSequenceMinorsNonnegative]
  intro r rows cols
  rw [hcoeff]
  exact betaNaturalCoefficient_minorsNonnegative (b := 0) (by positivity) rows cols

/-- A finite product of power series with totally nonnegative coefficient sequences retains the
same property. -/
theorem powerSeriesMinorsNonnegative_prod {ι : Type*} [Fintype ι]
    (f : ι → ℝ⟦X⟧) (hf : ∀ i, PowerSeriesMinorsNonnegative (f i)) :
    PowerSeriesMinorsNonnegative (∏ i, f i) := by
  classical
  exact Finset.prod_induction f PowerSeriesMinorsNonnegative
    (fun _ _ ha hb ↦ ha.mul hb)
    powerSeriesOne_minorsNonnegative
    (fun i _ ↦ hf i)

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- Every finite beta product has a totally nonnegative Toeplitz coefficient sequence. -/
theorem betaProduct_minorsNonnegative : PowerSeriesMinorsNonnegative D.betaProduct := by
  apply powerSeriesMinorsNonnegative_prod
  intro j
  exact betaFactor_minorsNonnegative (D.beta_pos j).le

/-- Every finite alpha product has a totally nonnegative Toeplitz coefficient sequence. -/
theorem alphaProduct_minorsNonnegative : PowerSeriesMinorsNonnegative D.alphaProduct := by
  apply powerSeriesMinorsNonnegative_prod
  intro i
  exact alphaFactor_minorsNonnegative (D.alpha_pos i).le

/-- The finite alpha/beta factor has a totally nonnegative Toeplitz coefficient sequence. -/
theorem finiteFactor_minorsNonnegative : PowerSeriesMinorsNonnegative D.finiteFactor := by
  rw [finiteFactor]
  exact PowerSeriesMinorsNonnegative.mul
    D.betaProduct_minorsNonnegative D.alphaProduct_minorsNonnegative

/-- Every Toeplitz minor of the finite alpha/beta factor is nonnegative. -/
theorem finiteFactorMinorsNonnegative : D.FiniteFactorMinorsNonnegative := by
  intro r rows cols
  exact D.finiteFactor_minorsNonnegative rows cols

/-- Every finite square Toeplitz section of the finite alpha/beta factor is totally
nonnegative. -/
theorem finiteFactorToeplitz_totallyNonnegative (N : ℕ) :
    TotallyNonnegative
      (fun i j : Fin (N + 1) ↦ D.finiteFactorSequence ((j : ℤ) - (i : ℤ))) := by
  intro k rows cols
  have hminor := D.finiteFactorMinorsNonnegative
    (truncationSelection rows) (truncationSelection cols)
  simpa [orderedMinor, finiteFactorOnlyMinor, oneSidedToeplitzMinor,
    oneSidedToeplitzMinorMatrix, truncationSelection, Matrix.submatrix] using hminor

end FiniteEdreiData

end

end ToeplitzPositroids
