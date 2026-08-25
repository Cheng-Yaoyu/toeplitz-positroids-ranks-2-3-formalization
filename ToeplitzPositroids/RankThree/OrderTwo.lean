import ToeplitzPositroids.Matrix.Toeplitz
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Order-two total nonnegativity for three-row Toeplitz matrices

This file formalizes the elementary identities, both directions, and part of the
equality criterion in Lemma 5 of the paper.  Coefficient vectors are stored in the
order `a_{-2}, a_{-1}, ..., a_{n-1}`, as in `rankThreeToeplitz`.
-/

namespace ToeplitzPositroids

open Set

variable {R : Type*} {n : ℕ}

/-- The indices at which a finite coefficient vector is strictly positive. -/
def positiveSupport [Zero R] [LT R] {m : ℕ} (a : Fin m → R) : Set (Fin m) :=
  {i | 0 < a i}

@[simp]
theorem mem_positiveSupport [Zero R] [LT R] {m : ℕ} (a : Fin m → R) (i : Fin m) :
    i ∈ positiveSupport a ↔ 0 < a i :=
  Iff.rfl

/-- A finite coefficient vector has interval positive support when every index between
two positive coefficients is also positive.  The empty and singleton supports qualify. -/
def HasIntervalPositiveSupport [Zero R] [LT R] {m : ℕ} (a : Fin m → R) : Prop :=
  (positiveSupport a).OrdConnected

theorem hasIntervalPositiveSupport_iff [Zero R] [Preorder R] {m : ℕ} (a : Fin m → R) :
    HasIntervalPositiveSupport a ↔
      ∀ i j k, 0 < a i → 0 < a j → i ≤ k → k ≤ j → 0 < a k := by
  rw [HasIntervalPositiveSupport, Set.ordConnected_def]
  constructor
  · intro h i j k hi hj hik hkj
    exact h hi hj ⟨hik, hkj⟩
  · rintro h i hi j hj k ⟨hik, hkj⟩
    exact h i j k hi hj hik hkj

/-- Adjacent discrete log-concavity for the stored coefficient vector of a
three-row, `n`-column Toeplitz matrix. -/
def DiscretelyLogConcave [Mul R] [LE R] (a : Fin (n + 2) → R) : Prop :=
  ∀ k : Fin n,
    a k.succ.castSucc * a k.succ.castSucc ≥
      a k.castSucc.castSucc * a k.succ.succ

/-- The ratio between two adjacent stored coefficients. -/
def coefficientRatio [Div R] (a : Fin (n + 2) → R) (k : Fin (n + 1)) : R :=
  a k.succ / a k.castSucc

@[simp]
theorem coefficientRatio_apply [Div R] (a : Fin (n + 2) → R) (k : Fin (n + 1)) :
    coefficientRatio a k = a k.succ / a k.castSucc :=
  rfl

/-- The order embedding whose image is an increasing pair. -/
def twoPointOrderEmbedding [LinearOrder R] (i j : R) (hij : i < j) : Fin 2 ↪o R :=
  OrderEmbedding.ofStrictMono ![i, j] <| by
    intro p q hpq
    fin_cases p <;> fin_cases q
    · simp at hpq
    · exact hij
    · simp at hpq
    · simp at hpq

@[simp]
theorem twoPointOrderEmbedding_zero [LinearOrder R] (i j : R) (hij : i < j) :
    twoPointOrderEmbedding i j hij 0 = i :=
  rfl

@[simp]
theorem twoPointOrderEmbedding_one [LinearOrder R] (i j : R) (hij : i < j) :
    twoPointOrderEmbedding i j hij 1 = j :=
  rfl

section Ring

variable [CommRing R]

/-- The determinant of an arbitrary two-row, two-column Toeplitz submatrix. -/
theorem toeplitzMatrix_orderedMinor_two (a : ℤ → R) (i₀ i₁ : Fin 3) (hi : i₀ < i₁)
    (j₀ j₁ : Fin n) (hj : j₀ < j₁) :
    orderedMinor (toeplitzMatrix 3 n a) (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) =
      a (j₀ - i₀) * a (j₁ - i₁) - a (j₁ - i₀) * a (j₀ - i₁) := by
  rw [orderedMinor_two]
  simp

/-- The general order-two Toeplitz minor in the offset notation of the paper. -/
theorem toeplitzMatrix_orderedMinor_two_offset (a : ℤ → R) (i₀ i₁ : Fin 3)
    (hi : i₀ < i₁) (j₀ j₁ : Fin n) (hj : j₀ < j₁) :
    orderedMinor (toeplitzMatrix 3 n a) (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) =
      a (j₀ - i₀) * a ((j₀ - i₀) + (j₁ - j₀) - (i₁ - i₀)) -
        a ((j₀ - i₀) + (j₁ - j₀)) *
          a ((j₀ - i₀) - (i₁ - i₀)) := by
  rw [toeplitzMatrix_orderedMinor_two]
  have h₁ : (j₁ : ℤ) - i₁ = (j₀ - i₀) + (j₁ - j₀) - (i₁ - i₀) := by
    omega
  have h₂ : (j₁ : ℤ) - i₀ = (j₀ - i₀) + (j₁ - j₀) := by
    omega
  have h₃ : (j₀ : ℤ) - i₁ = (j₀ - i₀) - (i₁ - i₀) := by
    omega
  rw [h₁, h₂, h₃]

/-- The exact two-by-two minor formula directly in finite coefficient-vector indices. -/
theorem rankThreeToeplitz_orderedMinor_two (a : Fin (n + 2) → R)
    (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ j₁ : Fin n) (hj : j₀ < j₁) :
    orderedMinor (rankThreeToeplitz a) (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) =
      a (finiteToeplitzIndex i₀ j₀) * a (finiteToeplitzIndex i₁ j₁) -
        a (finiteToeplitzIndex i₀ j₁) * a (finiteToeplitzIndex i₁ j₀) := by
  rw [rankThreeToeplitz_eq_finiteToeplitz, orderedMinor_two]
  simp

/-- A finite two-by-two Toeplitz minor vanishes exactly when its two diagonal
coefficient products agree. -/
theorem rankThreeToeplitz_orderedMinor_two_eq_zero_iff (a : Fin (n + 2) → R)
    (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ j₁ : Fin n) (hj : j₀ < j₁) :
    orderedMinor (rankThreeToeplitz a) (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) = 0 ↔
      a (finiteToeplitzIndex i₀ j₀) * a (finiteToeplitzIndex i₁ j₁) =
        a (finiteToeplitzIndex i₀ j₁) * a (finiteToeplitzIndex i₁ j₀) := by
  rw [rankThreeToeplitz_orderedMinor_two, sub_eq_zero]

end Ring

section Real

variable {a : Fin (n + 2) → ℝ}

/-- The explicit collection of all order-two Toeplitz inequalities. -/
def OrderTwoToeplitzInequalities (a : Fin (n + 2) → ℝ) : Prop :=
  ∀ (i₀ i₁ : Fin 3), i₀ < i₁ → ∀ (j₀ j₁ : Fin n), j₀ < j₁ →
    0 ≤ a (finiteToeplitzIndex i₀ j₀) * a (finiteToeplitzIndex i₁ j₁) -
      a (finiteToeplitzIndex i₀ j₁) * a (finiteToeplitzIndex i₁ j₀)

/-- Order-one total nonnegativity makes every displayed Toeplitz coefficient nonnegative. -/
theorem rankThreeToeplitz_coeff_nonneg (hn : 0 < n)
    (hA : TNUpTo (rankThreeToeplitz a) 2) (k : Fin (n + 2)) :
    0 ≤ a k := by
  by_cases hk : (k : ℕ) ≤ 2
  · let i : Fin 3 := ⟨2 - k, by omega⟩
    let j : Fin n := ⟨0, hn⟩
    have hentry := hA.entry_nonneg (by omega) i j
    rw [rankThreeToeplitz_apply] at hentry
    convert hentry using 1
    apply congrArg a
    apply Fin.ext
    simp only [i, j]
    omega
  · let i : Fin 3 := ⟨0, by omega⟩
    let j : Fin n := ⟨k - 2, by omega⟩
    have hentry := hA.entry_nonneg (by omega) i j
    rw [rankThreeToeplitz_apply] at hentry
    convert hentry using 1
    apply congrArg a
    apply Fin.ext
    simp only [i, j]
    omega

/-- Total nonnegativity through order two is exactly coefficientwise nonnegativity
together with the explicit family of order-two Toeplitz inequalities. -/
theorem rankThreeToeplitz_tnUpTo_two_iff_explicit (hn : 0 < n) :
    TNUpTo (rankThreeToeplitz a) 2 ↔
      (∀ k, 0 ≤ a k) ∧ OrderTwoToeplitzInequalities a := by
  constructor
  · intro hA
    refine ⟨rankThreeToeplitz_coeff_nonneg hn hA, ?_⟩
    intro i₀ i₁ hi j₀ j₁ hj
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj)
    rw [rankThreeToeplitz_orderedMinor_two] at hminor
    exact hminor
  · rintro ⟨ha, htwo⟩ l hl rows cols
    have hl' : l = 0 ∨ l = 1 ∨ l = 2 := by omega
    obtain rfl | rfl | rfl := hl'
    · simp
    · rw [orderedMinor_one]
      rw [rankThreeToeplitz_apply]
      exact ha _
    · have hrows : rows = twoPointOrderEmbedding (rows 0) (rows 1)
          (rows.strictMono (by decide)) := by
        ext i
        fin_cases i <;> rfl
      have hcols : cols = twoPointOrderEmbedding (cols 0) (cols 1)
          (cols.strictMono (by decide)) := by
        ext j
        fin_cases j <;> rfl
      rw [hrows, hcols, rankThreeToeplitz_orderedMinor_two]
      exact htwo _ _ (rows.strictMono (by decide)) _ _ (cols.strictMono (by decide))

/-- Two positive coefficients separated only by zero coefficients would force a
negative order-two minor. -/
theorem rankThreeToeplitz_no_positive_gap (hn : 3 ≤ n)
    (hA : TNUpTo (rankThreeToeplitz a) 2) {p q : Fin (n + 2)}
    (hpq : p.val + 1 < q.val) (hp : 0 < a p) (hq : 0 < a q)
    (hzero : ∀ k : Fin (n + 2), p < k → k < q → a k = 0) : False := by
  by_cases hp0 : p = 0
  · subst p
    by_cases hqlast : q = Fin.last (n + 1)
    · subst q
      let c₀ : Fin n := ⟨0, by omega⟩
      let c₁ : Fin n := ⟨n - 1, by omega⟩
      have hc : c₀ < c₁ := by simp [c₀, c₁]; omega
      have hr : (0 : Fin 3) < 2 := by decide
      have hleft : a c₀.succ.succ = 0 := by
        apply hzero
        · change (0 : ℕ) < (c₀.succ.succ).val
          simp [c₀]
        · change (c₀.succ.succ).val < (Fin.last (n + 1)).val
          simp [c₀]
          omega
      have hright : a c₁.castSucc.castSucc = 0 := by
        apply hzero
        · change (0 : ℕ) < (c₁.castSucc.castSucc).val
          simp [c₁]
          omega
        · change (c₁.castSucc.castSucc).val < (Fin.last (n + 1)).val
          simp [c₁]
      have hpentry : a c₀.castSucc.castSucc = a (0 : Fin (n + 2)) := by
        congr 1
      have hqentry : a c₁.succ.succ = a (Fin.last (n + 1)) := by
        congr 1
        apply Fin.ext
        simp [c₁]
        omega
      have hm := hA.orderedMinor_nonneg (by omega : 2 ≤ 2)
        (twoPointOrderEmbedding 0 2 hr) (twoPointOrderEmbedding c₀ c₁ hc)
      rw [orderedMinor_two] at hm
      simp only [twoPointOrderEmbedding_zero, twoPointOrderEmbedding_one,
        rankThreeToeplitz_row_zero, rankThreeToeplitz_row_two] at hm
      rw [hleft, hright, hpentry, hqentry] at hm
      exact (not_lt_of_ge hm) (by
        simpa [mul_comm] using neg_lt_zero.mpr (mul_pos hp hq))
    · have hqval : q.val ≤ n := by
        by_contra h
        apply hqlast
        apply Fin.ext
        simp
        omega
      let c₀ : Fin n := ⟨0, by omega⟩
      let c₁ : Fin n := ⟨q.val - 1, by omega⟩
      have hc : c₀ < c₁ := by simp [c₀, c₁]; omega
      have hr : (1 : Fin 3) < 2 := by decide
      have hleft : a c₀.succ.castSucc = 0 := by
        apply hzero
        · change (0 : ℕ) < (c₀.succ.castSucc).val
          simp [c₀]
        · change (c₀.succ.castSucc).val < q.val
          simp [c₀]
          omega
      have hright : a c₁.castSucc.castSucc = 0 := by
        apply hzero
        · change (0 : ℕ) < (c₁.castSucc.castSucc).val
          simp [c₁]
          omega
        · change (c₁.castSucc.castSucc).val < q.val
          simp [c₁]
          omega
      have hpentry : a c₀.castSucc.castSucc = a (0 : Fin (n + 2)) := by
        congr 1
      have hqentry : a c₁.succ.castSucc = a q := by
        congr 1
        apply Fin.ext
        simp [c₁]
        omega
      have hm := hA.orderedMinor_nonneg (by omega : 2 ≤ 2)
        (twoPointOrderEmbedding 1 2 hr) (twoPointOrderEmbedding c₀ c₁ hc)
      rw [orderedMinor_two] at hm
      simp only [twoPointOrderEmbedding_zero, twoPointOrderEmbedding_one,
        rankThreeToeplitz_row_one, rankThreeToeplitz_row_two] at hm
      rw [hleft, hright, hpentry, hqentry] at hm
      exact (not_lt_of_ge hm) (by
        simpa [mul_comm] using neg_lt_zero.mpr (mul_pos hp hq))
  · have hpval : 1 ≤ p.val := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro hpval0
      apply hp0
      apply Fin.ext
      simpa using hpval0
    let c₀ : Fin n := ⟨p.val - 1, by omega⟩
    let c₁ : Fin n := ⟨q.val - 2, by omega⟩
    have hc : c₀ < c₁ := by simp [c₀, c₁]; omega
    have hr : (0 : Fin 3) < 1 := by decide
    have hleft : a c₀.succ.succ = 0 := by
      apply hzero
      · change p.val < (c₀.succ.succ).val
        simp [c₀]
        omega
      · change (c₀.succ.succ).val < q.val
        simp [c₀]
        omega
    have hright : a c₁.succ.castSucc = 0 := by
      apply hzero
      · change p.val < (c₁.succ.castSucc).val
        simp [c₁]
        omega
      · change (c₁.succ.castSucc).val < q.val
        simp [c₁]
        omega
    have hpentry : a c₀.succ.castSucc = a p := by
      congr 1
      apply Fin.ext
      simp [c₀]
      omega
    have hqentry : a c₁.succ.succ = a q := by
      congr 1
      apply Fin.ext
      simp [c₁]
      omega
    have hm := hA.orderedMinor_nonneg (by omega : 2 ≤ 2)
      (twoPointOrderEmbedding 0 1 hr) (twoPointOrderEmbedding c₀ c₁ hc)
    rw [orderedMinor_two] at hm
    simp only [twoPointOrderEmbedding_zero, twoPointOrderEmbedding_one,
      rankThreeToeplitz_row_zero, rankThreeToeplitz_row_one] at hm
    rw [hleft, hright, hpentry, hqentry] at hm
    exact (not_lt_of_ge hm) (by
      simpa [mul_comm] using neg_lt_zero.mpr (mul_pos hp hq))

/-- A nonnegative finite sequence with no positive gap has interval positive support. -/
theorem positiveSupport_ordConnected_of_no_gap {m : ℕ} (b : Fin m → ℝ)
    (hnonneg : ∀ k, 0 ≤ b k)
    (hgap : ∀ {p q : Fin m}, p.val + 1 < q.val → 0 < b p → 0 < b q →
      (∀ k : Fin m, p < k → k < q → b k = 0) → False) :
    Set.OrdConnected {k : Fin m | 0 < b k} := by
  rw [Set.ordConnected_iff]
  intro i hi j hj hij k hk
  change 0 < b k
  by_contra hkpos
  have hkzero : b k = 0 := le_antisymm (le_of_not_gt hkpos) (hnonneg k)
  let left : Finset (Fin m) := (Finset.Icc i k).filter fun t ↦ 0 < b t
  have hi_left : i ∈ left := by
    simp only [left, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨le_rfl, hk.1⟩, hi⟩
  have hleft_nonempty : left.Nonempty := ⟨i, hi_left⟩
  let p : Fin m := left.max' hleft_nonempty
  have hp_left : p ∈ left := Finset.max'_mem left hleft_nonempty
  have hp_pos : 0 < b p := (Finset.mem_filter.mp hp_left).2
  have hp_le_k : p ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp_left).1).2
  have hp_lt_k : p < k := lt_of_le_of_ne hp_le_k fun hpk ↦ by
    exact hkpos (hpk ▸ hp_pos)
  let right : Finset (Fin m) := (Finset.Icc k j).filter fun t ↦ 0 < b t
  have hj_right : j ∈ right := by
    simp only [right, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hk.2, le_rfl⟩, hj⟩
  have hright_nonempty : right.Nonempty := ⟨j, hj_right⟩
  let q : Fin m := right.min' hright_nonempty
  have hq_right : q ∈ right := Finset.min'_mem right hright_nonempty
  have hq_pos : 0 < b q := (Finset.mem_filter.mp hq_right).2
  have hk_le_q : k ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hq_right).1).1
  have hk_lt_q : k < q := lt_of_le_of_ne hk_le_q fun hkq ↦ by
    exact hkpos (hkq.symm ▸ hq_pos)
  apply hgap (p := p) (q := q) (by omega) hp_pos hq_pos
  intro t hpt htq
  have ht_not_pos : ¬0 < b t := by
    intro htpos
    rcases le_total t k with htk | hkt
    · have ht_left : t ∈ left := by
        simp only [left, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hp_left).1).1.trans hpt.le,
          htk⟩, htpos⟩
      have htle : t ≤ p := (Finset.max'_le_iff left hleft_nonempty).mp le_rfl t ht_left
      exact (not_le_of_gt hpt) htle
    · have ht_right : t ∈ right := by
        simp only [right, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hkt, htq.le.trans
          (Finset.mem_Icc.mp (Finset.mem_filter.mp hq_right).1).2⟩, htpos⟩
      have hqle : q ≤ t := (Finset.le_min'_iff right hright_nonempty).mp le_rfl t ht_right
      exact (not_le_of_gt htq) hqle
  exact le_antisymm (le_of_not_gt ht_not_pos) (hnonneg t)

/-- Total nonnegativity through order two forces the positive coefficient support
to be an interval. -/
theorem rankThreeToeplitz_hasIntervalPositiveSupport (hn : 3 ≤ n)
    (hA : TNUpTo (rankThreeToeplitz a) 2) :
    HasIntervalPositiveSupport a := by
  apply positiveSupport_ordConnected_of_no_gap a
  · exact rankThreeToeplitz_coeff_nonneg (by omega) hA
  · intro p q hpq hp hq hzero
    exact rankThreeToeplitz_no_positive_gap hn hA hpq hp hq hzero

/-- At three consecutive positive coefficients, discrete log-concavity says that
the later adjacent ratio is no larger than the earlier one. -/
theorem coefficientRatio_succ_le (hlog : DiscretelyLogConcave a) (k : Fin n)
    (hleft : 0 < a k.castSucc.castSucc) (hcenter : 0 < a k.succ.castSucc) :
    coefficientRatio a k.succ ≤ coefficientRatio a k.castSucc := by
  rw [coefficientRatio_apply, coefficientRatio_apply,
    div_le_div_iff₀ hcenter hleft]
  have hcenterIndex : k.castSucc.succ = k.succ.castSucc := by
    apply Fin.ext
    rfl
  rw [hcenterIndex]
  simpa [mul_comm] using hlog k

/-- On a positive coefficient interval, adjacent ratios are weakly decreasing. -/
theorem coefficientRatio_le_of_le (hlog : DiscretelyLogConcave a)
    {p q : Fin (n + 1)} (hpq : p ≤ q)
    (hpos : ∀ t : Fin (n + 2), p.val ≤ t.val → t.val ≤ q.val + 1 → 0 < a t) :
    coefficientRatio a q ≤ coefficientRatio a p := by
  let f : ℕ → ℝ := fun t ↦
    if ht : t < n + 1 then coefficientRatio a ⟨t, ht⟩ else 0
  have hstep : ∀ t : ℕ, p.val ≤ t → t < q.val → f (t + 1) ≤ f t := by
    intro t hpt htq
    simp only [f, dif_pos (by omega : t + 1 < n + 1), dif_pos (by omega : t < n + 1)]
    apply coefficientRatio_succ_le hlog ⟨t, by omega⟩
    · apply hpos ⟨t, by omega⟩
      · change p.val ≤ t
        omega
      · change t ≤ q.val + 1
        omega
    · apply hpos ⟨t + 1, by omega⟩
      · change p.val ≤ t + 1
        omega
      · change t + 1 ≤ q.val + 1
        omega
  have hchain : ∀ t : ℕ, p.val ≤ t → t ≤ q.val → f t ≤ f p.val := by
    intro t hpt
    induction t, hpt using Nat.le_induction with
    | base =>
        intro _
        exact le_rfl
    | succ t hpt ih =>
        intro htq
        exact (hstep t hpt (by omega)).trans (ih (by omega))
  have h := hchain q.val (by omega) le_rfl
  simpa only [f, dif_pos (by omega : q.val < n + 1),
    dif_pos (by omega : p.val < n + 1), Fin.eta] using h

/-- The one-step cross-product inequality implied by interval support and discrete
log-concavity. -/
theorem oneStepToeplitzDifference_nonneg (hnonneg : ∀ k, 0 ≤ a k)
    (hsupport : HasIntervalPositiveSupport a) (hlog : DiscretelyLogConcave a)
    {p q : Fin (n + 1)} (hpq : p < q) :
    0 ≤ a p.succ * a q.castSucc - a q.succ * a p.castSucc := by
  have hfirstNonneg : 0 ≤ a p.succ * a q.castSucc :=
    mul_nonneg (hnonneg _) (hnonneg _)
  have hsecondNonneg : 0 ≤ a q.succ * a p.castSucc :=
    mul_nonneg (hnonneg _) (hnonneg _)
  by_cases hsecondPos : 0 < a q.succ * a p.castSucc
  · rcases mul_ne_zero_iff.mp (ne_of_gt hsecondPos) with ⟨hqne, hpne⟩
    have hleft : 0 < a p.castSucc := lt_of_le_of_ne (hnonneg _) (Ne.symm hpne)
    have hright : 0 < a q.succ := lt_of_le_of_ne (hnonneg _) (Ne.symm hqne)
    have hpos : ∀ t : Fin (n + 2), p.val ≤ t.val → t.val ≤ q.val + 1 → 0 < a t := by
      intro t hpt htq
      apply (hasIntervalPositiveSupport_iff a).mp hsupport p.castSucc q.succ t hleft hright
      · change p.val ≤ t.val
        exact hpt
      · change t.val ≤ q.val + 1
        exact htq
    have hratio := coefficientRatio_le_of_le hlog hpq.le hpos
    have hqden : 0 < a q.castSucc := by
      apply hpos q.castSucc
      · change p.val ≤ q.val
        exact hpq.le
      · change q.val ≤ q.val + 1
        omega
    rw [coefficientRatio_apply, coefficientRatio_apply,
      div_le_div_iff₀ hqden hleft] at hratio
    exact sub_nonneg.mpr hratio
  · have hsecondZero : a q.succ * a p.castSucc = 0 :=
      le_antisymm (le_of_not_gt hsecondPos) hsecondNonneg
    simpa [hsecondZero] using hfirstNonneg

/-- For positive denominators, a one-step Toeplitz difference vanishes exactly
when its endpoint coefficient ratios agree. -/
theorem oneStepToeplitzDifference_eq_zero_iff_ratio_eq {p q : Fin (n + 1)}
    (hp : 0 < a p.castSucc) (hq : 0 < a q.castSucc) :
    a p.succ * a q.castSucc - a q.succ * a p.castSucc = 0 ↔
      coefficientRatio a p = coefficientRatio a q := by
  rw [sub_eq_zero, coefficientRatio_apply, coefficientRatio_apply,
    div_eq_div_iff (ne_of_gt hp) (ne_of_gt hq)]

/-- Equality in a positive one-step Toeplitz inequality is equivalent to constancy
of every adjacent coefficient ratio between its endpoints. -/
theorem oneStepToeplitzDifference_eq_zero_iff_ratio_const
    (hsupport : HasIntervalPositiveSupport a) (hlog : DiscretelyLogConcave a)
    {p q : Fin (n + 1)} (hpq : p ≤ q)
    (hleft : 0 < a p.castSucc) (hright : 0 < a q.succ) :
    a p.succ * a q.castSucc - a q.succ * a p.castSucc = 0 ↔
      ∀ t : Fin (n + 1), p ≤ t → t ≤ q →
        coefficientRatio a t = coefficientRatio a p := by
  have hpos : ∀ t : Fin (n + 2), p.val ≤ t.val → t.val ≤ q.val + 1 → 0 < a t := by
    intro t hpt htq
    apply (hasIntervalPositiveSupport_iff a).mp hsupport p.castSucc q.succ t hleft hright
    · change p.val ≤ t.val
      exact hpt
    · change t.val ≤ q.val + 1
      exact htq
  have hqden : 0 < a q.castSucc := by
    apply hpos q.castSucc
    · change p.val ≤ q.val
      exact hpq
    · change q.val ≤ q.val + 1
      omega
  rw [oneStepToeplitzDifference_eq_zero_iff_ratio_eq hleft hqden]
  constructor
  · intro hpqRatio t hpt htq
    have htp := coefficientRatio_le_of_le hlog hpt (fun u hu₀ hu₁ ↦
      hpos u (by omega) (by omega))
    have hqt := coefficientRatio_le_of_le hlog htq (fun u hu₀ hu₁ ↦
      hpos u (by omega) (by omega))
    apply le_antisymm htp
    rw [hpqRatio]
    exact hqt
  · intro hconst
    exact (hconst q hpq le_rfl).symm

/-- The two-step cross-product inequality implied by interval support and discrete
log-concavity. -/
theorem twoStepToeplitzDifference_nonneg (hnonneg : ∀ k, 0 ≤ a k)
    (hsupport : HasIntervalPositiveSupport a) (hlog : DiscretelyLogConcave a)
    {p q : Fin n} (hpq : p < q) :
    0 ≤ a p.succ.succ * a q.castSucc.castSucc -
      a q.succ.succ * a p.castSucc.castSucc := by
  have hfirstNonneg : 0 ≤ a p.succ.succ * a q.castSucc.castSucc :=
    mul_nonneg (hnonneg _) (hnonneg _)
  have hsecondNonneg : 0 ≤ a q.succ.succ * a p.castSucc.castSucc :=
    mul_nonneg (hnonneg _) (hnonneg _)
  by_cases hsecondPos : 0 < a q.succ.succ * a p.castSucc.castSucc
  · rcases mul_ne_zero_iff.mp (ne_of_gt hsecondPos) with ⟨hqne, hpne⟩
    have hleft : 0 < a p.castSucc.castSucc :=
      lt_of_le_of_ne (hnonneg _) (Ne.symm hpne)
    have hright : 0 < a q.succ.succ := lt_of_le_of_ne (hnonneg _) (Ne.symm hqne)
    have hpos : ∀ t : Fin (n + 2), p.val ≤ t.val → t.val ≤ q.val + 2 → 0 < a t := by
      intro t hpt htq
      apply (hasIntervalPositiveSupport_iff a).mp hsupport
        p.castSucc.castSucc q.succ.succ t hleft hright
      · change p.val ≤ t.val
        exact hpt
      · change t.val ≤ q.val + 2
        exact htq
    have hratio₀ := coefficientRatio_le_of_le hlog
      (show p.castSucc ≤ q.castSucc by simpa using hpq.le)
      (by
        intro t hpt htq
        simp only [Fin.val_castSucc] at hpt htq
        exact hpos t hpt (by omega))
    have hratio₁ := coefficientRatio_le_of_le hlog
      (show p.succ ≤ q.succ by simpa using hpq.le)
      (by
        intro t hpt htq
        simp only [Fin.val_succ] at hpt htq
        exact hpos t (by omega) htq)
    have hq₀ : 0 < a q.castSucc.castSucc := by
      apply hpos q.castSucc.castSucc
      · change p.val ≤ q.val
        exact hpq.le
      · change q.val ≤ q.val + 2
        omega
    have hq₁ : 0 < a q.succ.castSucc := by
      apply hpos q.succ.castSucc
      · change p.val ≤ q.val + 1
        omega
      · change q.val + 1 ≤ q.val + 2
        omega
    have hp₁ : 0 < a p.succ.castSucc := by
      apply hpos p.succ.castSucc
      · change p.val ≤ p.val + 1
        omega
      · change p.val + 1 ≤ q.val + 2
        omega
    have hp₂ : 0 < a p.succ.succ := by
      apply hpos p.succ.succ
      · change p.val ≤ p.val + 2
        omega
      · change p.val + 2 ≤ q.val + 2
        omega
    have hqcenter : q.castSucc.succ = q.succ.castSucc := by
      apply Fin.ext
      rfl
    have hpcenter : p.castSucc.succ = p.succ.castSucc := by
      apply Fin.ext
      rfl
    have hratioQ₀ : 0 ≤ coefficientRatio a q.castSucc := by
      rw [coefficientRatio_apply, hqcenter]
      exact (div_pos hq₁ hq₀).le
    have hratioP₁ : 0 ≤ coefficientRatio a p.succ := by
      rw [coefficientRatio_apply]
      exact (div_pos hp₂ hp₁).le
    have hprod := mul_le_mul hratio₁ hratio₀ hratioQ₀ hratioP₁
    have hqprod : coefficientRatio a q.succ * coefficientRatio a q.castSucc =
        a q.succ.succ / a q.castSucc.castSucc := by
      simp only [coefficientRatio_apply]
      rw [hqcenter]
      field_simp [ne_of_gt hq₀, ne_of_gt hq₁]
    have hpprod : coefficientRatio a p.succ * coefficientRatio a p.castSucc =
        a p.succ.succ / a p.castSucc.castSucc := by
      simp only [coefficientRatio_apply]
      rw [hpcenter]
      field_simp [ne_of_gt hleft, ne_of_gt hp₁]
    rw [hqprod, hpprod] at hprod
    rw [div_le_div_iff₀ hq₀ hleft] at hprod
    exact sub_nonneg.mpr (by simpa [mul_comm] using hprod)
  · have hsecondZero : a q.succ.succ * a p.castSucc.castSucc = 0 :=
      le_antisymm (le_of_not_gt hsecondPos) hsecondNonneg
    simpa [hsecondZero] using hfirstNonneg

/-- Coefficientwise nonnegativity, interval positive support, and adjacent discrete
log-concavity imply every explicit order-two Toeplitz inequality. -/
theorem orderTwoToeplitzInequalities_of_logConcave (hnonneg : ∀ i, 0 ≤ a i)
    (hsupport : HasIntervalPositiveSupport a) (hlog : DiscretelyLogConcave a) :
    OrderTwoToeplitzInequalities a := by
  intro i₀ i₁ hi j₀ j₁ hj
  fin_cases i₀ <;> fin_cases i₁ <;> simp at hi
  · have h := oneStepToeplitzDifference_nonneg hnonneg hsupport hlog
      (p := j₀.succ) (q := j₁.succ) (by simpa using hj)
    simpa [finiteToeplitzIndex] using h
  · have h := twoStepToeplitzDifference_nonneg hnonneg hsupport hlog
      (p := j₀) (q := j₁) hj
    simpa [finiteToeplitzIndex] using h
  · have h := oneStepToeplitzDifference_nonneg hnonneg hsupport hlog
      (p := j₀.castSucc) (q := j₁.castSucc) (by simpa using hj)
    simpa [finiteToeplitzIndex] using h

/-- A bottom-two-row adjacent minor is an adjacent log-concavity difference. -/
theorem rankThreeToeplitz_bottom_adjacent_minor (a : Fin (n + 2) → ℝ)
    (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    orderedMinor (rankThreeToeplitz a)
        (twoPointOrderEmbedding (1 : Fin 3) 2 (by decide))
        (twoPointOrderEmbedding j ⟨j + 1, hj⟩ (by
          change j.val < j.val + 1
          exact Nat.lt_succ_self _)) =
      a j.succ.castSucc * a j.succ.castSucc -
        a j.castSucc.castSucc * a j.succ.succ := by
  rw [rankThreeToeplitz_orderedMinor_two]
  have h₀₀ : finiteToeplitzIndex (1 : Fin 3) j = j.succ.castSucc := by
    apply Fin.ext
    simp
  have h₁₁ : finiteToeplitzIndex (2 : Fin 3) (⟨j + 1, hj⟩ : Fin n) =
      j.succ.castSucc := by
    apply Fin.ext
    simp
  have h₀₁ : finiteToeplitzIndex (1 : Fin 3) (⟨j + 1, hj⟩ : Fin n) =
      j.succ.succ := by
    apply Fin.ext
    simp
  have h₁₀ : finiteToeplitzIndex (2 : Fin 3) j = j.castSucc.castSucc := by
    apply Fin.ext
    simp
  rw [h₀₀, h₁₁, h₀₁, h₁₀]
  ring

/-- A top-two-row adjacent minor is the next adjacent log-concavity difference. -/
theorem rankThreeToeplitz_top_adjacent_minor (a : Fin (n + 2) → ℝ)
    (j : Fin n) (hj : (j : ℕ) + 1 < n) :
    orderedMinor (rankThreeToeplitz a)
        (twoPointOrderEmbedding (0 : Fin 3) 1 (by decide))
        (twoPointOrderEmbedding j ⟨j + 1, hj⟩ (by
          change j.val < j.val + 1
          exact Nat.lt_succ_self _)) =
      a j.succ.succ * a j.succ.succ -
        a j.succ.castSucc * a (⟨j + 1, hj⟩ : Fin n).succ.succ := by
  rw [rankThreeToeplitz_orderedMinor_two]
  have h₀₀ : finiteToeplitzIndex (0 : Fin 3) j = j.succ.succ := by
    apply Fin.ext
    simp
  have h₁₁ : finiteToeplitzIndex (1 : Fin 3) (⟨j + 1, hj⟩ : Fin n) =
      j.succ.succ := by
    apply Fin.ext
    simp
  have h₀₁ : finiteToeplitzIndex (0 : Fin 3) (⟨j + 1, hj⟩ : Fin n) =
      (⟨j + 1, hj⟩ : Fin n).succ.succ := by
    apply Fin.ext
    simp
  have h₁₀ : finiteToeplitzIndex (1 : Fin 3) j = j.succ.castSucc := by
    apply Fin.ext
    simp
  rw [h₀₀, h₁₁, h₀₁, h₁₀]
  ring_nf

/-- Total nonnegativity through order two forces adjacent discrete log-concavity. -/
theorem rankThreeToeplitz_discretelyLogConcave (hn : 2 ≤ n)
    (hA : TNUpTo (rankThreeToeplitz a) 2) :
    DiscretelyLogConcave a := by
  intro k
  by_cases hk : (k : ℕ) + 1 < n
  · have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding (1 : Fin 3) 2 (by decide))
      (twoPointOrderEmbedding k ⟨k + 1, hk⟩ (by
        change k.val < k.val + 1
        exact Nat.lt_succ_self _))
    rw [rankThreeToeplitz_bottom_adjacent_minor] at hminor
    exact sub_nonneg.mp hminor
  · let j : Fin n := ⟨n - 2, by omega⟩
    have hj : (j : ℕ) + 1 < n := by simp only [j]; omega
    have hminor := hA.orderedMinor_nonneg le_rfl
      (twoPointOrderEmbedding (0 : Fin 3) 1 (by decide))
      (twoPointOrderEmbedding j ⟨j + 1, hj⟩ (by
        change j.val < j.val + 1
        exact Nat.lt_succ_self _))
    rw [rankThreeToeplitz_top_adjacent_minor] at hminor
    have hk' : (k : ℕ) = n - 1 := by omega
    have hineq := sub_nonneg.mp hminor
    have hleft : k.castSucc.castSucc = j.succ.castSucc := by
      apply Fin.ext
      simp [j]
      omega
    have hcenter : k.succ.castSucc = j.succ.succ := by
      apply Fin.ext
      simp [j]
      omega
    have hright : k.succ.succ = (⟨j + 1, hj⟩ : Fin n).succ.succ := by
      apply Fin.ext
      simp [j]
      omega
    rw [hleft, hcenter, hright]
    exact hineq

/-- The three coefficient conditions in the order-two criterion are necessary. -/
theorem rankThreeToeplitz_orderTwo_necessary (hn : 3 ≤ n)
    (hA : TNUpTo (rankThreeToeplitz a) 2) :
    (∀ k, 0 ≤ a k) ∧ HasIntervalPositiveSupport a ∧ DiscretelyLogConcave a := by
  exact ⟨rankThreeToeplitz_coeff_nonneg (by omega) hA,
    rankThreeToeplitz_hasIntervalPositiveSupport hn hA,
    rankThreeToeplitz_discretelyLogConcave (by omega) hA⟩

/-- The order-two Toeplitz criterion (Lemma 5): a three-row Toeplitz section is
totally nonnegative through order two exactly when its coefficients are nonnegative,
their positive support is an interval, and they are discretely log-concave. -/
theorem rankThreeToeplitz_tnUpTo_two_iff (hn : 3 ≤ n) :
    TNUpTo (rankThreeToeplitz a) 2 ↔
      (∀ k, 0 ≤ a k) ∧ HasIntervalPositiveSupport a ∧ DiscretelyLogConcave a := by
  constructor
  · exact rankThreeToeplitz_orderTwo_necessary hn
  · rintro ⟨hnonneg, hsupport, hlog⟩
    rw [rankThreeToeplitz_tnUpTo_two_iff_explicit (by omega)]
    exact ⟨hnonneg, orderTwoToeplitzInequalities_of_logConcave hnonneg hsupport hlog⟩

end Real

end ToeplitzPositroids
