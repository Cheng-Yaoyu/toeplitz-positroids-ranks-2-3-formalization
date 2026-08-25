import ToeplitzPositroids.Edrei.FactorialKernelGeneral
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

/-!
# Arbitrary reciprocal-factorial minors

This file proves strict positivity of every structurally allowed minor of the
reciprocal-factorial Toeplitz kernel.  The proof is an induction on the total
componentwise gap.  Its key identity is the determinant recurrence obtained by
lowering one selected column at a time.
-/

namespace ToeplitzPositroids

noncomputable section

/-- The total componentwise gap between two increasing tuples. -/
def factorialTupleGap {r : ℕ} (rows cols : Fin r ↪o ℕ) : ℕ :=
  Finset.univ.sum fun i : Fin r ↦ cols i - rows i

/-- Lower the coefficient index in one matrix column by one. -/
def factorialKernelDecrementMatrix {r : ℕ} (rows cols : Fin r ↪o ℕ)
    (j : Fin r) : Matrix (Fin r) (Fin r) ℝ :=
  fun i k ↦ factorialKernelCoefficient
    ((cols k : ℤ) - (rows i : ℤ) - if k = j then 1 else 0)

/-- Multiplying a reciprocal-factorial coefficient by its integer index lowers
that index by one. -/
theorem int_mul_factorialKernelCoefficient (k : ℤ) :
    (k : ℝ) * factorialKernelCoefficient k = factorialKernelCoefficient (k - 1) := by
  by_cases hk : k < 0
  · have hk1 : k - 1 < 0 := by omega
    rw [factorialKernelCoefficient_eq_zero_of_neg hk,
      factorialKernelCoefficient_eq_zero_of_neg hk1, mul_zero]
  · have hk0 : 0 ≤ k := by omega
    have hrepr : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
    rw [← hrepr]
    cases k.toNat with
    | zero => norm_num [factorialKernelCoefficient]
    | succ n =>
        have hidx : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
        rw [hidx, factorialKernelCoefficient_ofNat, factorialKernelCoefficient_ofNat,
          Nat.factorial_succ]
        push_cast
        have hn : ((n.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp

/-- A column can be lowered while preserving both strict increase and structural
admissibility. -/
def FactorialColumnDecrementable {r : ℕ} (rows cols : Fin r ↪o ℕ)
    (j : Fin r) : Prop :=
  rows j < cols j ∧ ∀ k, k < j → cols k < cols j - 1

/-- Lower one entry of an increasing column tuple. -/
def decrementNaturalColumns {r : ℕ} (cols : Fin r ↪o ℕ) (j : Fin r)
    (hjpos : 0 < cols j) (hsep : ∀ k, k < j → cols k < cols j - 1) : Fin r ↪o ℕ :=
  OrderEmbedding.ofStrictMono (fun k ↦ if k = j then cols k - 1 else cols k) (by
    intro a b hab
    by_cases haj : a = j
    · subst a
      simp only [if_pos, if_neg hab.ne']
      exact (Nat.sub_lt (by omega) (by omega)).trans (cols.strictMono hab)
    by_cases hbj : b = j
    · subst b
      simp only [if_neg haj, if_pos]
      exact hsep a hab
    · simp only [if_neg haj, if_neg hbj]
      exact cols.strictMono hab)

@[simp]
theorem decrementNaturalColumns_apply_self {r : ℕ} (cols : Fin r ↪o ℕ) (j : Fin r)
    (hjpos : 0 < cols j) (hsep : ∀ k, k < j → cols k < cols j - 1) :
    decrementNaturalColumns cols j hjpos hsep j = cols j - 1 := by
  simp [decrementNaturalColumns]

theorem decrementNaturalColumns_apply_of_ne {r : ℕ} (cols : Fin r ↪o ℕ) (j k : Fin r)
    (hjpos : 0 < cols j) (hsep : ∀ l, l < j → cols l < cols j - 1)
    (hkj : k ≠ j) :
    decrementNaturalColumns cols j hjpos hsep k = cols k := by
  simp [decrementNaturalColumns, hkj]

/-- The lowered-column matrix is the factorial-kernel matrix of the lowered
tuple whenever the latter is well-defined. -/
theorem factorialKernelDecrementMatrix_eq_minorMatrix {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (j : Fin r)
    (hjpos : 0 < cols j) (hsep : ∀ k, k < j → cols k < cols j - 1) :
    factorialKernelDecrementMatrix rows cols j =
      oneSidedToeplitzMinorMatrix factorialKernelCoefficient rows
        (decrementNaturalColumns cols j hjpos hsep) := by
  ext i k
  simp only [factorialKernelDecrementMatrix, oneSidedToeplitzMinorMatrix_apply,
    decrementNaturalColumns, OrderEmbedding.coe_ofStrictMono]
  by_cases hkj : k = j
  · subst k
    simp only [if_pos]
    congr 1
    omega
  · simp only [if_neg hkj, sub_zero]

/-- Lowering an admissible column reduces the total gap by exactly one. -/
theorem factorialTupleGap_decrement {r : ℕ} (rows cols : Fin r ↪o ℕ)
    (j : Fin r) (hgap : rows j < cols j)
    (hsep : ∀ k, k < j → cols k < cols j - 1) :
    factorialTupleGap rows
        (decrementNaturalColumns cols j (Nat.zero_lt_of_lt hgap) hsep) =
      factorialTupleGap rows cols - 1 := by
  unfold factorialTupleGap
  rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ j),
    Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_univ j)]
  rw [decrementNaturalColumns_apply_self]
  have hrest :
      Finset.sum (Finset.univ \ {j}) (fun x ↦
          decrementNaturalColumns cols j (Nat.zero_lt_of_lt hgap) hsep x - rows x) =
        Finset.sum (Finset.univ \ {j}) (fun x ↦ cols x - rows x) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkj : k ≠ j := by
      intro h
      subst k
      exact (Finset.notMem_sdiff_of_mem_right (by simp)) hk
    simp [decrementNaturalColumns, hkj]
  rw [hrest]
  omega

/-- A decrementable column remains componentwise above the selected rows. -/
theorem decrementNaturalColumns_allowed {r : ℕ} (rows cols : Fin r ↪o ℕ)
    (hallowed : ∀ i, rows i ≤ cols i) (j : Fin r)
    (hdec : FactorialColumnDecrementable rows cols j) :
    ∀ i, rows i ≤
      decrementNaturalColumns cols j (Nat.zero_lt_of_lt hdec.1) hdec.2 i := by
  intro i
  by_cases hij : i = j
  · subst i
    rw [decrementNaturalColumns_apply_self]
    have hj := hdec.1
    omega
  · rw [decrementNaturalColumns_apply_of_ne _ _ _ _ _ hij]
    exact hallowed i

/-- For a decrementable column, the lowered determinant is the corresponding
reciprocal-factorial minor. -/
theorem factorialKernelDecrementMatrix_det_eq_minor {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (j : Fin r)
    (hdec : FactorialColumnDecrementable rows cols j) :
    (factorialKernelDecrementMatrix rows cols j).det =
      factorialKernelMinor rows
        (decrementNaturalColumns cols j (Nat.zero_lt_of_lt hdec.1) hdec.2) := by
  rw [factorialKernelMinor, oneSidedToeplitzMinor,
    factorialKernelDecrementMatrix_eq_minorMatrix]

/-- Lowering a zero column gives the zero matrix column. -/
theorem factorialKernelDecrementMatrix_det_eq_zero_of_col_zero {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (j : Fin r) (hj : cols j = 0) :
    (factorialKernelDecrementMatrix rows cols j).det = 0 := by
  apply Matrix.det_eq_zero_of_column_eq_zero j
  intro i
  unfold factorialKernelDecrementMatrix
  rw [if_pos rfl]
  apply factorialKernelCoefficient_eq_zero_of_neg
  rw [hj]
  omega

/-- If lowering a column makes it equal an earlier selected column, its
determinant vanishes. -/
theorem factorialKernelDecrementMatrix_det_eq_zero_of_collision {r : ℕ}
    (rows cols : Fin r ↪o ℕ) {k j : Fin r} (hkj : k < j)
    (hcols : cols k = cols j - 1) :
    (factorialKernelDecrementMatrix rows cols j).det = 0 := by
  apply Matrix.det_zero_of_column_eq hkj.ne
  intro i
  unfold factorialKernelDecrementMatrix
  rw [if_neg hkj.ne, if_pos rfl, sub_zero]
  congr 1
  have hstrict := cols.strictMono hkj
  rw [hcols, Nat.cast_sub (by omega : 1 ≤ cols j)]
  push_cast
  ring

/-- Failure of the separation condition produces an earlier colliding column. -/
theorem exists_factorialColumn_collision {r : ℕ} (cols : Fin r ↪o ℕ)
    (j : Fin r) (hsep : ¬∀ k, k < j → cols k < cols j - 1) :
    ∃ k, k < j ∧ cols k = cols j - 1 := by
  simp only [not_forall, not_lt] at hsep
  obtain ⟨k, hkj, hsep⟩ := hsep
  refine ⟨k, hkj, ?_⟩
  have hstrict := cols.strictMono hkj
  omega

/-- Every non-decrementable lowered-column determinant is zero. -/
theorem factorialKernelDecrementMatrix_det_eq_zero_of_not_decrementable {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (j : Fin r) (hdec : ¬FactorialColumnDecrementable rows cols j) :
    (factorialKernelDecrementMatrix rows cols j).det = 0 := by
  by_cases hjzero : cols j = 0
  · exact factorialKernelDecrementMatrix_det_eq_zero_of_col_zero rows cols j hjzero
  have hjpos : 0 < cols j := Nat.pos_of_ne_zero hjzero
  by_cases hsep : ∀ k, k < j → cols k < cols j - 1
  · have hroweq : rows j = cols j := by
      apply le_antisymm (hallowed j)
      by_contra hne
      apply hdec
      exact ⟨by omega, hsep⟩
    rw [factorialKernelDecrementMatrix_eq_minorMatrix rows cols j hjpos hsep]
    apply oneSidedToeplitzMinor_eq_zero_of_not_componentwise_le
      (h := factorialKernelCoefficient)
    · intro z hz
      exact factorialKernelCoefficient_eq_zero_of_neg hz
    · simp only [not_forall, not_le]
      refine ⟨j, ?_⟩
      rw [decrementNaturalColumns_apply_self]
      omega
  · obtain ⟨k, hkj, hk⟩ := exists_factorialColumn_collision cols j hsep
    exact factorialKernelDecrementMatrix_det_eq_zero_of_collision rows cols hkj hk

private theorem sum_mul_prod_eq_sum_mul_prod_erase {ι : Type*}
    [Fintype ι] [DecidableEq ι] (k a b : ι → ℝ) (h : ∀ i, k i * a i = b i) :
    (∑ i, k i) * (∏ i, a i) =
      ∑ i, b i * ∏ x ∈ Finset.univ.erase i, a x := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    k i * (∏ x, a x) = k i * (a i * ∏ x ∈ Finset.univ.erase i, a x) := by
      rw [Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)]
    _ = (k i * a i) * ∏ x ∈ Finset.univ.erase i, a x := by ring
    _ = b i * ∏ x ∈ Finset.univ.erase i, a x := by rw [h i]

/-- The total gap is the sum of the integer coefficient indices in every
Leibniz term. -/
theorem factorialTupleGap_cast_eq_sum_perm {r : ℕ} (rows cols : Fin r ↪o ℕ)
    (hallowed : ∀ i, rows i ≤ cols i) (σ : Equiv.Perm (Fin r)) :
    (factorialTupleGap rows cols : ℝ) =
      ∑ j : Fin r, (((cols j : ℤ) - (rows (σ j) : ℤ) : ℤ) : ℝ) := by
  have hperm : (∑ j : Fin r, (rows (σ j) : ℝ)) = ∑ j : Fin r, (rows j : ℝ) := by
    exact Fintype.sum_equiv σ _ _ fun _ ↦ rfl
  unfold factorialTupleGap
  push_cast [Nat.cast_sub (hallowed _)]
  rw [Finset.sum_sub_distrib]
  calc
    (∑ x : Fin r, (cols x : ℝ)) - ∑ x : Fin r, (rows x : ℝ) =
        (∑ x : Fin r, (cols x : ℝ)) - ∑ x : Fin r, (rows (σ x) : ℝ) := by
          rw [hperm]
    _ = ∑ x : Fin r, ((cols x : ℝ) - (rows (σ x) : ℝ)) :=
      (Finset.sum_sub_distrib (fun x : Fin r ↦ (cols x : ℝ))
        (fun x : Fin r ↦ (rows (σ x) : ℝ))).symm

private theorem factorialKernelDecrementMatrix_term {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (σ : Equiv.Perm (Fin r)) (j : Fin r) :
    (∏ k : Fin r, factorialKernelDecrementMatrix rows cols j (σ k) k) =
      factorialKernelCoefficient ((cols j : ℤ) - (rows (σ j) : ℤ) - 1) *
        ∏ k ∈ Finset.univ.erase j,
          factorialKernelCoefficient ((cols k : ℤ) - (rows (σ k) : ℤ)) := by
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ j)]
  unfold factorialKernelDecrementMatrix
  rw [if_pos rfl]
  congr 1
  rw [Finset.sdiff_singleton_eq_erase]
  apply Finset.prod_congr rfl
  intro k hk
  have hkj : k ≠ j := by
    intro h
    subst k
    exact (Finset.notMem_erase j Finset.univ) hk
  rw [if_neg hkj, sub_zero]

/-- The scalar gap times one Leibniz product is the sum of the products with
one column lowered. -/
theorem factorialTupleGap_mul_leibnizProduct {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (σ : Equiv.Perm (Fin r)) :
    (factorialTupleGap rows cols : ℝ) *
        (∏ j : Fin r, factorialKernelCoefficient
          ((cols j : ℤ) - (rows (σ j) : ℤ))) =
      ∑ j : Fin r,
        ∏ k : Fin r, factorialKernelDecrementMatrix rows cols j (σ k) k := by
  rw [factorialTupleGap_cast_eq_sum_perm rows cols hallowed σ]
  rw [sum_mul_prod_eq_sum_mul_prod_erase
    (fun j : Fin r ↦ (((cols j : ℤ) - (rows (σ j) : ℤ) : ℤ) : ℝ))
    (fun j : Fin r ↦ factorialKernelCoefficient
      ((cols j : ℤ) - (rows (σ j) : ℤ)))
    (fun j : Fin r ↦ factorialKernelCoefficient
      ((cols j : ℤ) - (rows (σ j) : ℤ) - 1))]
  · apply Finset.sum_congr rfl
    intro j hj
    exact (factorialKernelDecrementMatrix_term rows cols σ j).symm
  · intro j
    exact int_mul_factorialKernelCoefficient _

/-- Lowering-column recurrence for the reciprocal-factorial determinant. -/
theorem factorialTupleGap_mul_factorialKernelMinor {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    (factorialTupleGap rows cols : ℝ) * factorialKernelMinor rows cols =
      ∑ j : Fin r, (factorialKernelDecrementMatrix rows cols j).det := by
  unfold factorialKernelMinor oneSidedToeplitzMinor
  simp only [Matrix.det_apply, oneSidedToeplitzMinorMatrix_apply, Units.smul_def,
    zsmul_eq_mul]
  rw [Finset.mul_sum]
  calc
    (∑ σ : Equiv.Perm (Fin r),
        (factorialTupleGap rows cols : ℝ) *
          ((Equiv.Perm.sign σ : ℝ) *
            ∏ i : Fin r, factorialKernelCoefficient
              ((cols i : ℤ) - (rows (σ i) : ℤ)))) =
        ∑ σ : Equiv.Perm (Fin r),
          (Equiv.Perm.sign σ : ℝ) *
            ((factorialTupleGap rows cols : ℝ) *
              ∏ i : Fin r, factorialKernelCoefficient
                ((cols i : ℤ) - (rows (σ i) : ℤ))) := by
          apply Finset.sum_congr rfl
          intro σ hσ
          ring
    _ = ∑ σ : Equiv.Perm (Fin r),
          (Equiv.Perm.sign σ : ℝ) *
            ∑ j : Fin r,
              ∏ k : Fin r, factorialKernelDecrementMatrix rows cols j (σ k) k := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [factorialTupleGap_mul_leibnizProduct rows cols hallowed σ]
    _ = ∑ σ : Equiv.Perm (Fin r), ∑ j : Fin r,
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k : Fin r, factorialKernelDecrementMatrix rows cols j (σ k) k := by
          apply Finset.sum_congr rfl
          intro σ hσ
          rw [Finset.mul_sum]
    _ = ∑ j : Fin r, ∑ σ : Equiv.Perm (Fin r),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k : Fin r, factorialKernelDecrementMatrix rows cols j (σ k) k := by
          rw [Finset.sum_comm]

/-- Zero total gap forces the two increasing tuples to coincide. -/
theorem orderEmbeddings_eq_of_factorialTupleGap_eq_zero {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (hgap : factorialTupleGap rows cols = 0) :
    rows = cols := by
  apply RelEmbedding.ext
  intro i
  apply le_antisymm (hallowed i)
  have hzero : cols i - rows i = 0 := by
    apply (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hgap
    exact Finset.mem_univ i
  omega

/-- Positive total gap supplies a column that can be lowered admissibly. -/
theorem exists_factorialColumnDecrementable {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (hgap : 0 < factorialTupleGap rows cols) :
    ∃ j, FactorialColumnDecrementable rows cols j := by
  let S : Finset (Fin r) := Finset.univ.filter fun i ↦ rows i < cols i
  have hS : S.Nonempty := by
    rw [factorialTupleGap] at hgap
    obtain ⟨j, hjmem, hjpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun _ _ ↦ Nat.zero_le _)).mp hgap
    refine ⟨j, ?_⟩
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  let j : Fin r := S.min' hS
  have hjmem : j ∈ S := S.min'_mem hS
  have hjgap : rows j < cols j := by
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hjmem
  refine ⟨j, hjgap, ?_⟩
  intro k hkj
  have hknot : k ∉ S := by
    intro hkmem
    have hjk := S.min'_le k hkmem
    exact (not_lt_of_ge hjk) hkj
  have hkeq : rows k = cols k := by
    have hnotlt : ¬rows k < cols k := by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hknot
    exact le_antisymm (hallowed k) (not_lt.mp hnotlt)
  have hrows := rows.strictMono hkj
  omega

/-- Every componentwise-allowed reciprocal-factorial minor is strictly
positive, with no restriction on the increasing row tuple. -/
theorem factorialKernelMinor_arbitraryRows_pos {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    0 < factorialKernelMinor rows cols := by
  generalize hN : factorialTupleGap rows cols = N
  induction N using Nat.strong_induction_on generalizing cols with
  | h N ih =>
      by_cases hNzero : N = 0
      · have hrowscols : rows = cols :=
          orderEmbeddings_eq_of_factorialTupleGap_eq_zero rows cols hallowed
            (hN.trans hNzero)
        subst cols
        rw [factorialKernelMinor,
          oneSidedToeplitzMinor_principal
            (fun _ hk ↦ factorialKernelCoefficient_eq_zero_of_neg hk)
            (by norm_num [factorialKernelCoefficient])]
        norm_num
      · have hNpos : 0 < N := Nat.pos_of_ne_zero hNzero
        have hgapPos : 0 < factorialTupleGap rows cols := by omega
        have hterm_nonneg :
            ∀ j : Fin r, 0 ≤ (factorialKernelDecrementMatrix rows cols j).det := by
          intro j
          by_cases hdec : FactorialColumnDecrementable rows cols j
          · rw [factorialKernelDecrementMatrix_det_eq_minor rows cols j hdec]
            have hallowed' := decrementNaturalColumns_allowed rows cols hallowed j hdec
            have hgap' := factorialTupleGap_decrement rows cols j hdec.1 hdec.2
            have hlt : factorialTupleGap rows
                (decrementNaturalColumns cols j (Nat.zero_lt_of_lt hdec.1) hdec.2) < N := by
              omega
            exact (ih _ hlt _ hallowed' rfl).le
          · rw [factorialKernelDecrementMatrix_det_eq_zero_of_not_decrementable
              rows cols hallowed j hdec]
        obtain ⟨j, hjdec⟩ := exists_factorialColumnDecrementable rows cols hallowed hgapPos
        have hterm_pos : 0 < (factorialKernelDecrementMatrix rows cols j).det := by
          rw [factorialKernelDecrementMatrix_det_eq_minor rows cols j hjdec]
          have hallowed' := decrementNaturalColumns_allowed rows cols hallowed j hjdec
          have hgap' := factorialTupleGap_decrement rows cols j hjdec.1 hjdec.2
          have hlt : factorialTupleGap rows
              (decrementNaturalColumns cols j (Nat.zero_lt_of_lt hjdec.1) hjdec.2) < N := by
            omega
          exact ih _ hlt _ hallowed' rfl
        have hsum : 0 < ∑ j : Fin r,
            (factorialKernelDecrementMatrix rows cols j).det := by
          apply Finset.sum_pos'
          · intro k hk
            exact hterm_nonneg k
          · exact ⟨j, Finset.mem_univ j, hterm_pos⟩
        rw [← factorialTupleGap_mul_factorialKernelMinor rows cols hallowed] at hsum
        have hcast : (0 : ℝ) < factorialTupleGap rows cols := by exact_mod_cast hgapPos
        exact (mul_pos_iff_of_pos_left hcast).mp hsum

/-- Unconditional arbitrary-row form of the generalized Pascal theorem. -/
theorem factorialKernelMinor_pos {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    0 < factorialKernelMinor rows cols :=
  factorialKernelMinor_arbitraryRows_pos rows cols hallowed

/-- Exact support criterion for arbitrary reciprocal-factorial minors. -/
theorem factorialKernelMinor_pos_iff_componentwise_le {r : ℕ}
    (rows cols : Fin r ↪o ℕ) :
    0 < factorialKernelMinor rows cols ↔ ∀ i, rows i ≤ cols i := by
  constructor
  · intro hpos
    by_contra hbad
    rw [factorialKernelMinor, oneSidedToeplitzMinor_eq_zero_of_not_componentwise_le
      (h := factorialKernelCoefficient)
      (fun _ hk ↦ factorialKernelCoefficient_eq_zero_of_neg hk) rows cols hbad] at hpos
    exact lt_irrefl 0 hpos
  · exact factorialKernelMinor_pos rows cols

/-- Every structurally allowed exponential Toeplitz minor is strictly positive
for a positive exponential parameter. -/
theorem exponentialToeplitzMinor_arbitraryRows_pos {r : ℕ} {gamma : ℝ}
    (hgamma : 0 < gamma) (rows cols : Fin r ↪o ℕ)
    (hallowed : ∀ i, rows i ≤ cols i) :
    0 < exponentialToeplitzMinor gamma rows cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma rows cols).2
    (factorialKernelMinor_pos rows cols hallowed)

/-- Exact support criterion for the positive exponential specialization. -/
theorem exponentialToeplitzMinor_pos_iff_componentwise_le {r : ℕ} {gamma : ℝ}
    (hgamma : 0 < gamma) (rows cols : Fin r ↪o ℕ) :
    0 < exponentialToeplitzMinor gamma rows cols ↔ ∀ i, rows i ≤ cols i := by
  rw [exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma rows cols,
    factorialKernelMinor_pos_iff_componentwise_le]

end

end ToeplitzPositroids
