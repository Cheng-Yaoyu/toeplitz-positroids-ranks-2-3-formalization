import ToeplitzPositroids.Matrix.Configuration
import ToeplitzPositroids.Matrix.Toeplitz
import ToeplitzPositroids.RankTwo.Basic
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Classification of rank-two Toeplitz configurations

This file develops the matrix-level content of the rank-two classification.  The canonical
Toeplitz wrapper is `rankTwoToeplitz`; the older shifted wrapper is related to it once and is not
used in the classification statements.

The necessity direction proves interval support for the coefficients and nonloop columns,
monotonicity of projective column parameters with the rays `0` and `∞` included, convexity of
positive-parallel classes, and the endpoint singleton restrictions forced by adjacent loops.
The final section gives a quantified realization theorem for the loop-free finite-projective
chart, including exact control of its parallel classes.
-/

namespace ToeplitzPositroids

open Matrix Set

variable {n blocks : ℕ}

/-- The shifted wrapper introduced before the common Toeplitz API is definitionally the canonical
rank-two wrapper. -/
theorem shiftedRankTwoToeplitz_eq_rankTwoToeplitz {R : Type*}
    (a : Fin (n + 1) → R) :
    shiftedRankTwoToeplitz a = rankTwoToeplitz a := by
  ext i j
  fin_cases i <;> rfl

/-- The increasing map whose range is the ordered pair `i < j`. -/
def pairOrderEmbedding {α : Type*} [LinearOrder α] (i j : α) (hij : i < j) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono ![i, j] <| by
    intro x y hxy
    fin_cases x <;> fin_cases y
    · simp at hxy
    · exact hij
    · simp at hxy
    · simp at hxy

@[simp]
theorem pairOrderEmbedding_zero {α : Type*} [LinearOrder α] (i j : α) (hij : i < j) :
    pairOrderEmbedding i j hij 0 = i :=
  rfl

@[simp]
theorem pairOrderEmbedding_one {α : Type*} [LinearOrder α] (i j : α) (hij : i < j) :
    pairOrderEmbedding i j hij 1 = j :=
  rfl

/-- Total nonnegativity makes every increasingly ordered pair minor nonnegative. -/
theorem orderedPairMinor_nonneg_of_totallyNonnegative
    {A : Matrix (Fin 2) (Fin n) ℝ} (hA : TotallyNonnegative A)
    {i j : Fin n} (hij : i < j) :
    0 ≤ orderedPairMinor A i j := by
  have hminor := hA.orderedMinor_nonneg (allRows 2) (pairOrderEmbedding i j hij)
  rw [orderedMinor_two] at hminor
  simpa [allRows, orderedPairMinor] using hminor

/-- The pair-minor formula for the canonical rank-two Toeplitz wrapper. -/
@[simp]
theorem orderedPairMinor_rankTwoToeplitz (a : Fin (n + 1) → ℝ) (i j : Fin n) :
    orderedPairMinor (rankTwoToeplitz a) i j =
      a i.succ * a j.castSucc - a j.succ * a i.castSucc := by
  simp only [orderedPairMinor, rankTwoToeplitz_row_zero, rankTwoToeplitz_row_one]

/-- If there is at least one column, total nonnegativity makes every stored coefficient
nonnegative. -/
theorem rankTwoToeplitz_coefficient_nonneg (a : Fin (n + 1) → ℝ) (hn : 0 < n)
    (hA : TotallyNonnegative (rankTwoToeplitz a)) (k : Fin (n + 1)) :
    0 ≤ a k := by
  by_cases hk : k = Fin.last n
  · subst k
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simpa using hA.entry_nonneg (0 : Fin 2) (Fin.last d)
  · simpa using hA.entry_nonneg (1 : Fin 2) (k.castPred hk)

/-- A rank-two Toeplitz column is a loop exactly when its two adjacent coefficients vanish. -/
theorem rankTwoToeplitz_isLoop_iff (a : Fin (n + 1) → ℝ) (j : Fin n) :
    IsLoop (rankTwoToeplitz a) j ↔ a j.succ = 0 ∧ a j.castSucc = 0 := by
  rw [isLoop_iff_entry_eq_zero]
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨hu, hl⟩ i
    fin_cases i
    · simpa using hu
    · simpa using hl

/-- Under coefficientwise nonnegativity, a column is a nonloop exactly when at least one of its
two coefficients is positive. -/
theorem rankTwoToeplitz_not_isLoop_iff (a : Fin (n + 1) → ℝ)
    (ha : ∀ k, 0 ≤ a k) (j : Fin n) :
    ¬IsLoop (rankTwoToeplitz a) j ↔ 0 < a j.succ ∨ 0 < a j.castSucc := by
  rw [rankTwoToeplitz_isLoop_iff]
  constructor
  · intro h
    by_cases hu : a j.succ = 0
    · right
      exact lt_of_le_of_ne (ha _) (Ne.symm fun hl ↦ h ⟨hu, hl⟩)
    · left
      exact lt_of_le_of_ne (ha _) (Ne.symm hu)
  · rintro (hu | hl) h
    · exact hu.ne' h.1
    · exact hl.ne' h.2

/-- A zero coefficient with a positive coefficient strictly to its left forces the next
coefficient to vanish.  The proof uses the nonconsecutive pair minor selected by those two
coefficient positions. -/
theorem rankTwoToeplitz_coefficient_succ_eq_zero
    (a : Fin (n + 1) → ℝ) (hn : 0 < n)
    (hA : TotallyNonnegative (rankTwoToeplitz a))
    {p k : Fin n} (hpk : p < k) (hp : 0 < a p.castSucc) (hk : a k.castSucc = 0) :
    a k.succ = 0 := by
  have hminor := orderedPairMinor_nonneg_of_totallyNonnegative hA hpk
  rw [orderedPairMinor_rankTwoToeplitz, hk, mul_zero, zero_sub] at hminor
  have hnext : 0 ≤ a k.succ := rankTwoToeplitz_coefficient_nonneg a hn hA k.succ
  have hprod_nonneg : 0 ≤ a k.succ * a p.castSucc := mul_nonneg hnext hp.le
  have hprod : a k.succ * a p.castSucc = 0 := le_antisymm (by linarith) hprod_nonneg
  exact (mul_eq_zero.mp hprod).resolve_right hp.ne'

/-- Once a zero occurs strictly to the right of a positive coefficient, all later coefficients in
the finite section vanish. -/
theorem rankTwoToeplitz_coefficient_zero_propagates_right
    (a : Fin (n + 1) → ℝ) (hn : 0 < n)
    (hA : TotallyNonnegative (rankTwoToeplitz a))
    (p : Fin (n + 1)) (hp : 0 < a p) (k l : ℕ)
    (hpk : p.val < k) (hkl : k ≤ l) (hl : l ≤ n)
    (hk : a ⟨k, by omega⟩ = 0) :
    a ⟨l, by omega⟩ = 0 := by
  revert hl hk
  refine Nat.le_induction ?_ ?_ l hkl
  · intro _ hk
    exact hk
  · intro t hkt ih ht hk
    let pp : Fin n := ⟨p.val, by omega⟩
    let tt : Fin n := ⟨t, by omega⟩
    have hp' : 0 < a pp.castSucc := by
      simpa [pp] using hp
    have htzero : a tt.castSucc = 0 := by
      simpa [tt] using ih (by omega) hk
    have hpt : pp < tt := by
      simpa [pp, tt] using (show p.val < t by omega)
    have hnext := rankTwoToeplitz_coefficient_succ_eq_zero a hn hA hpt hp' htzero
    simpa [tt] using hnext

/-- The positive support of the coefficient vector of a totally nonnegative rank-two Toeplitz
matrix is an ordinary interval. -/
theorem rankTwoToeplitz_positiveSupport_ordConnected
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a)) :
    Set.OrdConnected {k | 0 < a k} := by
  cases n with
  | zero =>
      rw [Set.ordConnected_iff]
      intro x hx y _ _ z _
      fin_cases x
      fin_cases y
      fin_cases z
      exact hx
  | succ d =>
      rw [Set.ordConnected_iff]
      intro p hp q hq hpq k hk
      change 0 < a k
      by_contra hnot
      have hak : 0 ≤ a k :=
        rankTwoToeplitz_coefficient_nonneg a (Nat.succ_pos d) hA k
      have hkzero : a k = 0 := le_antisymm (not_lt.mp hnot) hak
      rcases eq_or_lt_of_le hk.1 with rfl | hpk
      · exact hp.ne' hkzero
      have hprop := rankTwoToeplitz_coefficient_zero_propagates_right
        a (Nat.succ_pos d) hA p hp k.val q.val hpk hk.2
        (by omega) (by simpa using hkzero)
      exact hq.ne' (by simpa using hprop)

/-- The nonloop columns of a totally nonnegative rank-two Toeplitz matrix form an ordinary
interval. -/
theorem rankTwoToeplitz_nonloop_ordConnected
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a)) :
    Set.OrdConnected {j | ¬IsLoop (rankTwoToeplitz a) j} := by
  cases n with
  | zero =>
      rw [Set.ordConnected_iff]
      intro i
      exact Fin.elim0 i
  | succ d =>
      have hn : 0 < d + 1 := Nat.succ_pos d
      have ha : ∀ k, 0 ≤ a k := rankTwoToeplitz_coefficient_nonneg a hn hA
      have hs := rankTwoToeplitz_positiveSupport_ordConnected a hA
      rw [Set.ordConnected_iff]
      intro i hi k hk hik j hj
      change ¬IsLoop (rankTwoToeplitz a) j
      rcases eq_or_lt_of_le hj.1 with rfl | hij
      · exact hi
      rcases (rankTwoToeplitz_not_isLoop_iff a ha i).mp hi with hiu | hil <;>
      rcases (rankTwoToeplitz_not_isLoop_iff a ha k).mp hk with hku | hkl
      · have hjpos : 0 < a j.castSucc :=
          hs.out hiu hku ⟨by change i.val + 1 ≤ j.val; exact hij,
            by change j.val ≤ k.val + 1; exact Nat.le_succ_of_le hj.2⟩
        exact (rankTwoToeplitz_not_isLoop_iff a ha j).mpr (Or.inr hjpos)
      · have hjpos : 0 < a j.castSucc :=
          hs.out hiu hkl ⟨by change i.val + 1 ≤ j.val; exact hij,
            by change j.val ≤ k.val; exact hj.2⟩
        exact (rankTwoToeplitz_not_isLoop_iff a ha j).mpr (Or.inr hjpos)
      · have hjpos : 0 < a j.castSucc :=
          hs.out hil hku ⟨by change i.val ≤ j.val; exact hj.1,
            by change j.val ≤ k.val + 1; exact Nat.le_succ_of_le hj.2⟩
        exact (rankTwoToeplitz_not_isLoop_iff a ha j).mpr (Or.inr hjpos)
      · have hjpos : 0 < a j.castSucc :=
          hs.out hil hkl ⟨by change i.val ≤ j.val; exact hj.1,
            by change j.val ≤ k.val; exact hj.2⟩
        exact (rankTwoToeplitz_not_isLoop_iff a ha j).mpr (Or.inr hjpos)

/-- The projective coordinate `lower / upper`, with a zero upper coordinate represented by the
terminal ray `∞`. -/
noncomputable def rankTwoProjectiveParameterWithTop
    (a : Fin (n + 1) → ℝ) (j : Fin n) : WithTop ℝ :=
  if a j.succ = 0 then ⊤ else (a j.castSucc / a j.succ : ℝ)

/-- On the nonloop interval, total nonnegativity makes the extended projective parameter weakly
increasing.  This statement includes both the initial ray `0` and the terminal ray `∞`. -/
theorem rankTwoProjectiveParameterWithTop_mono
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a))
    {i j : Fin n} (hij : i ≤ j)
    (hi : ¬IsLoop (rankTwoToeplitz a) i) (hj : ¬IsLoop (rankTwoToeplitz a) j) :
    rankTwoProjectiveParameterWithTop a i ≤ rankTwoProjectiveParameterWithTop a j := by
  rcases eq_or_lt_of_le hij with rfl | hij
  · exact le_rfl
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have ha : ∀ k, 0 ≤ a k := rankTwoToeplitz_coefficient_nonneg a hn hA
  have hminor := orderedPairMinor_nonneg_of_totallyNonnegative hA hij
  by_cases hiu : a i.succ = 0
  · have hilne : a i.castSucc ≠ 0 := by
      intro hil
      exact hi ((rankTwoToeplitz_isLoop_iff a i).mpr ⟨hiu, hil⟩)
    have hilpos : 0 < a i.castSucc := lt_of_le_of_ne (ha _) (Ne.symm hilne)
    rw [orderedPairMinor_rankTwoToeplitz, hiu, zero_mul, zero_sub] at hminor
    have hprod_nonneg : 0 ≤ a j.succ * a i.castSucc := mul_nonneg (ha _) hilpos.le
    have hprod : a j.succ * a i.castSucc = 0 :=
      le_antisymm (by linarith) hprod_nonneg
    have hju : a j.succ = 0 := (mul_eq_zero.mp hprod).resolve_right hilpos.ne'
    simp [rankTwoProjectiveParameterWithTop, hiu, hju]
  · by_cases hju : a j.succ = 0
    · simp [rankTwoProjectiveParameterWithTop, hiu, hju]
    · have hiupos : 0 < a i.succ := lt_of_le_of_ne (ha _) (Ne.symm hiu)
      have hjupos : 0 < a j.succ := lt_of_le_of_ne (ha _) (Ne.symm hju)
      have hquot : a i.castSucc / a i.succ ≤ a j.castSucc / a j.succ := by
        apply (div_le_div_iff₀ hiupos hjupos).2
        rw [orderedPairMinor_rankTwoToeplitz] at hminor
        linarith
      simpa [rankTwoProjectiveParameterWithTop, hiu, hju] using hquot

/-- Two nonzero nonnegative columns of height two with zero determinant are positively
parallel. -/
theorem columnsPositivelyParallel_of_orderedPairMinor_eq_zero
    {A : Matrix (Fin 2) (Fin n) ℝ} {i j : Fin n}
    (hentry : ∀ r k, 0 ≤ A r k) (hi : ¬IsLoop A i) (hj : ¬IsLoop A j)
    (hminor : orderedPairMinor A i j = 0) :
    ColumnsPositivelyParallel A i j := by
  by_cases hiu : A 0 i = 0
  · have hilne : A 1 i ≠ 0 := by
      intro hil
      apply hi
      rw [isLoop_iff_entry_eq_zero]
      intro r
      fin_cases r
      · exact hiu
      · exact hil
    have hilpos : 0 < A 1 i := lt_of_le_of_ne (hentry 1 i) (Ne.symm hilne)
    have hju : A 0 j = 0 := by
      unfold orderedPairMinor at hminor
      rw [hiu, zero_mul, zero_sub, neg_eq_zero] at hminor
      exact (mul_eq_zero.mp hminor).resolve_right hilne
    have hjlne : A 1 j ≠ 0 := by
      intro hjl
      apply hj
      rw [isLoop_iff_entry_eq_zero]
      intro r
      fin_cases r
      · exact hju
      · exact hjl
    have hjlpos : 0 < A 1 j := lt_of_le_of_ne (hentry 1 j) (Ne.symm hjlne)
    refine ⟨A 1 j / A 1 i, div_pos hjlpos hilpos, ?_⟩
    ext r
    fin_cases r
    · simp [hiu, hju]
    · simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      change A 1 j = A 1 j / A 1 i * A 1 i
      rw [div_mul_cancel₀ _ hilne]
  · have hiupos : 0 < A 0 i := lt_of_le_of_ne (hentry 0 i) (Ne.symm hiu)
    have hju : A 0 j ≠ 0 := by
      intro hju
      have hjl : A 1 j = 0 := by
        unfold orderedPairMinor at hminor
        rw [hju, zero_mul, sub_zero] at hminor
        exact (mul_eq_zero.mp hminor).resolve_left hiu
      apply hj
      rw [isLoop_iff_entry_eq_zero]
      intro r
      fin_cases r
      · exact hju
      · exact hjl
    have hjupos : 0 < A 0 j := lt_of_le_of_ne (hentry 0 j) (Ne.symm hju)
    refine ⟨A 0 j / A 0 i, div_pos hjupos hiupos, ?_⟩
    ext r
    fin_cases r
    · simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      change A 0 j = A 0 j / A 0 i * A 0 i
      rw [div_mul_cancel₀ _ hiu]
    · simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul]
      change A 1 j = A 0 j / A 0 i * A 1 i
      unfold orderedPairMinor at hminor
      field_simp
      simpa [mul_comm] using (sub_eq_zero.mp hminor)

/-- On nonloop columns, equality of the extended projective parameters is equivalent to a zero
ordered pair minor. -/
theorem rankTwoProjectiveParameterWithTop_eq_iff_pairMinor_eq_zero
    (a : Fin (n + 1) → ℝ)
    {i j : Fin n} (hi : ¬IsLoop (rankTwoToeplitz a) i)
    (hj : ¬IsLoop (rankTwoToeplitz a) j) :
    rankTwoProjectiveParameterWithTop a i = rankTwoProjectiveParameterWithTop a j ↔
      orderedPairMinor (rankTwoToeplitz a) i j = 0 := by
  constructor
  · intro hq
    by_cases hiu : a i.succ = 0
    · have hju : a j.succ = 0 := by
        by_contra hju
        simp [rankTwoProjectiveParameterWithTop, hiu, hju] at hq
      simp [orderedPairMinor_rankTwoToeplitz, hiu, hju]
    · have hju : a j.succ ≠ 0 := by
        intro hju
        simp [rankTwoProjectiveParameterWithTop, hiu, hju] at hq
      have hreal : a i.castSucc / a i.succ = a j.castSucc / a j.succ := by
        simpa [rankTwoProjectiveParameterWithTop, hiu, hju] using hq
      rw [orderedPairMinor_rankTwoToeplitz, sub_eq_zero]
      field_simp [hiu, hju] at hreal
      simpa [mul_comm] using hreal.symm
  · intro hminor
    by_cases hiu : a i.succ = 0
    · have hilne : a i.castSucc ≠ 0 := by
        intro hil
        exact hi ((rankTwoToeplitz_isLoop_iff a i).mpr ⟨hiu, hil⟩)
      have hju : a j.succ = 0 := by
        rw [orderedPairMinor_rankTwoToeplitz, hiu, zero_mul, zero_sub,
          neg_eq_zero] at hminor
        exact (mul_eq_zero.mp hminor).resolve_right hilne
      simp [rankTwoProjectiveParameterWithTop, hiu, hju]
    · have hju : a j.succ ≠ 0 := by
        intro hju
        have hjlne : a j.castSucc ≠ 0 := by
          intro hjl
          exact hj ((rankTwoToeplitz_isLoop_iff a j).mpr ⟨hju, hjl⟩)
        rw [orderedPairMinor_rankTwoToeplitz, hju, zero_mul, sub_zero] at hminor
        exact hjlne ((mul_eq_zero.mp hminor).resolve_left hiu)
      have hcross : a i.castSucc * a j.succ = a j.castSucc * a i.succ := by
        rw [orderedPairMinor_rankTwoToeplitz, sub_eq_zero] at hminor
        simpa [mul_comm] using hminor.symm
      have hreal : a i.castSucc / a i.succ = a j.castSucc / a j.succ := by
        field_simp [hiu, hju]
        simpa [mul_comm] using hcross
      simpa [rankTwoProjectiveParameterWithTop, hiu, hju] using hreal

/-- Equality fibers of the extended projective parameter are exactly the positive-parallel
classes of nonloop columns. -/
theorem rankTwoProjectiveParameterWithTop_eq_iff_columnsPositivelyParallel
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a))
    {i j : Fin n} (hi : ¬IsLoop (rankTwoToeplitz a) i)
    (hj : ¬IsLoop (rankTwoToeplitz a) j) :
    rankTwoProjectiveParameterWithTop a i = rankTwoProjectiveParameterWithTop a j ↔
      ColumnsPositivelyParallel (rankTwoToeplitz a) i j := by
  rw [rankTwoProjectiveParameterWithTop_eq_iff_pairMinor_eq_zero a hi hj]
  constructor
  · exact columnsPositivelyParallel_of_orderedPairMinor_eq_zero
      (fun r k ↦ hA.entry_nonneg r k) hi hj
  · rintro ⟨c, -, hcol⟩
    exact orderedPairMinor_eq_zero_of_column_eq_smul _ _ _ c hcol

/-- A positive multiple of a nonloop column is again a nonloop column. -/
theorem columnsPositivelyParallel_not_isLoop_right
    {A : Matrix (Fin 2) (Fin n) ℝ} {i j : Fin n}
    (hij : ColumnsPositivelyParallel A i j) (hi : ¬IsLoop A i) :
    ¬IsLoop A j := by
  obtain ⟨c, hc, hcol⟩ := hij
  intro hj
  apply hi
  rw [isLoop_iff_entry_eq_zero]
  intro r
  have hcoord := congrFun hcol r
  have hjzero := (isLoop_iff_entry_eq_zero.mp hj) r
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  rw [hjzero] at hcoord
  exact (mul_eq_zero.mp hcoord.symm).resolve_left hc.ne'

/-- Every positive-parallel class among the nonloop columns is an ordinary interval. -/
theorem rankTwoToeplitz_parallelClasses_ordConnected
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a))
    {i : Fin n} (hi : ¬IsLoop (rankTwoToeplitz a) i) :
    Set.OrdConnected {j | ColumnsPositivelyParallel (rankTwoToeplitz a) i j} := by
  rw [Set.ordConnected_iff]
  intro p hp q hq hpq j hj
  have hpnonloop : ¬IsLoop (rankTwoToeplitz a) p :=
    columnsPositivelyParallel_not_isLoop_right hp hi
  have hqnonloop : ¬IsLoop (rankTwoToeplitz a) q :=
    columnsPositivelyParallel_not_isLoop_right hq hi
  have hjnonloop : ¬IsLoop (rankTwoToeplitz a) j :=
    (rankTwoToeplitz_nonloop_ordConnected a hA).out hpnonloop hqnonloop hj
  rcases eq_or_lt_of_le hj.1 with rfl | hpj
  · exact hp
  rcases eq_or_lt_of_le hj.2 with rfl | hjq
  · exact hq
  have hpqparallel := columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hp) hq
  obtain ⟨c, hc, hcol⟩ := hpqparallel
  have hpjminor := orderedPairMinor_nonneg_of_totallyNonnegative hA hpj
  have hjqminor := orderedPairMinor_nonneg_of_totallyNonnegative hA hjq
  have h₀ := congrFun hcol (0 : Fin 2)
  have h₁ := congrFun hcol (1 : Fin 2)
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at h₀ h₁
  have hrel : orderedPairMinor (rankTwoToeplitz a) j q =
      -c * orderedPairMinor (rankTwoToeplitz a) p j := by
    unfold orderedPairMinor
    rw [h₀, h₁]
    ring
  have hcmul_le : c * orderedPairMinor (rankTwoToeplitz a) p j ≤ 0 := by
    rw [hrel] at hjqminor
    linarith
  have hcmul_nonneg : 0 ≤ c * orderedPairMinor (rankTwoToeplitz a) p j :=
    mul_nonneg hc.le hpjminor
  have hminorzero : orderedPairMinor (rankTwoToeplitz a) p j = 0 := by
    have hmulzero := le_antisymm hcmul_le hcmul_nonneg
    exact (mul_eq_zero.mp hmulzero).resolve_left hc.ne'
  have hpjparallel := columnsPositivelyParallel_of_orderedPairMinor_eq_zero
    (i := p) (j := j) (fun r s ↦ hA.entry_nonneg r s) hpnonloop hjnonloop hminorzero
  exact columnsPositivelyParallel_trans hp hpjparallel

/-- Immediately after a loop, a nonloop column cannot be parallel to the following column. -/
theorem rankTwoToeplitz_not_parallel_next_of_previous_loop
    (a : Fin (n + 1) → ℝ) (i : Fin n) (hi0 : 0 < i.val) (hinext : i.val + 1 < n)
    (hprev : IsLoop (rankTwoToeplitz a) ⟨i.val - 1, by omega⟩)
    (hi : ¬IsLoop (rankTwoToeplitz a) i) :
    ¬ColumnsPositivelyParallel (rankTwoToeplitz a) i ⟨i.val + 1, hinext⟩ := by
  let prev : Fin n := ⟨i.val - 1, by omega⟩
  let next : Fin n := ⟨i.val + 1, hinext⟩
  have hai : a i.castSucc = 0 := by
    have hz := (isLoop_iff_entry_eq_zero.mp hprev) (0 : Fin 2)
    change a prev.succ = 0 at hz
    have hindex : prev.succ = i.castSucc := by
      apply Fin.ext
      simp [prev]
      omega
    rwa [hindex] at hz
  have haisucc : a i.succ ≠ 0 := by
    intro hz
    exact hi ((rankTwoToeplitz_isLoop_iff a i).mpr ⟨hz, hai⟩)
  rintro ⟨c, hc, hcol⟩
  have hcoord := congrFun hcol (1 : Fin 2)
  simp only [Matrix.col_apply, rankTwoToeplitz_row_one, Pi.smul_apply, smul_eq_mul] at hcoord
  have hnextIndex : next.castSucc = i.succ := by
    apply Fin.ext
    simp [next]
  rw [hnextIndex, hai, mul_zero] at hcoord
  exact haisucc hcoord

/-- Immediately before a loop, a nonloop column cannot be parallel to the preceding column. -/
theorem rankTwoToeplitz_not_parallel_previous_of_next_loop
    (a : Fin (n + 1) → ℝ) (i : Fin n) (hiprev : 0 < i.val) (hinext : i.val + 1 < n)
    (hnext : IsLoop (rankTwoToeplitz a) ⟨i.val + 1, hinext⟩)
    (hi : ¬IsLoop (rankTwoToeplitz a) i) :
    ¬ColumnsPositivelyParallel (rankTwoToeplitz a) ⟨i.val - 1, by omega⟩ i := by
  let prev : Fin n := ⟨i.val - 1, by omega⟩
  let next : Fin n := ⟨i.val + 1, hinext⟩
  have haisucc : a i.succ = 0 := by
    have hz := (isLoop_iff_entry_eq_zero.mp hnext) (1 : Fin 2)
    change a next.castSucc = 0 at hz
    simpa [next] using hz
  have hai : a i.castSucc ≠ 0 := by
    intro hz
    exact hi ((rankTwoToeplitz_isLoop_iff a i).mpr ⟨haisucc, hz⟩)
  rintro ⟨c, hc, hcol⟩
  have hcoord := congrFun hcol (0 : Fin 2)
  simp only [Matrix.col_apply, rankTwoToeplitz_row_zero, Pi.smul_apply, smul_eq_mul] at hcoord
  have hprevIndex : prev.succ = i.castSucc := by
    apply Fin.ext
    simp [prev]
    omega
  rw [haisucc, hprevIndex] at hcoord
  exact hai ((mul_eq_zero.mp hcoord.symm).resolve_left hc.ne')

/-- A nonloop column immediately following a loop forms a singleton parallel class. -/
theorem rankTwoToeplitz_initial_parallel_class_singleton
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a))
    (i : Fin n) (hi0 : 0 < i.val)
    (hprev : IsLoop (rankTwoToeplitz a) ⟨i.val - 1, by omega⟩)
    (hi : ¬IsLoop (rankTwoToeplitz a) i) (j : Fin n) :
    ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔ j = i := by
  constructor
  · intro hij
    rcases lt_trichotomy j i with hji | rfl | hijlt
    · have hjnonloop := columnsPositivelyParallel_not_isLoop_right hij hi
      let prev : Fin n := ⟨i.val - 1, by omega⟩
      have hprevnonloop : ¬IsLoop (rankTwoToeplitz a) prev :=
        (rankTwoToeplitz_nonloop_ordConnected a hA).out hjnonloop hi
          ⟨by change j.val ≤ prev.val; simp [prev]; omega,
            by change prev.val ≤ i.val; simp [prev]⟩
      exact False.elim (hprevnonloop (by simpa [prev] using hprev))
    · rfl
    · have hinext : i.val + 1 < n := by omega
      let next : Fin n := ⟨i.val + 1, hinext⟩
      have hnextparallel : ColumnsPositivelyParallel (rankTwoToeplitz a) i next :=
        (rankTwoToeplitz_parallelClasses_ordConnected a hA hi).out
          (columnsPositivelyParallel_refl _ _) hij
          ⟨by change i.val ≤ next.val; simp [next],
            by change next.val ≤ j.val; simp [next]; omega⟩
      exact False.elim
        ((rankTwoToeplitz_not_parallel_next_of_previous_loop a i hi0 hinext hprev hi)
          (by simpa [next] using hnextparallel))
  · rintro rfl
    exact columnsPositivelyParallel_refl _ _

/-- A nonloop column immediately preceding a loop forms a singleton parallel class. -/
theorem rankTwoToeplitz_terminal_parallel_class_singleton
    (a : Fin (n + 1) → ℝ) (hA : TotallyNonnegative (rankTwoToeplitz a))
    (i : Fin n) (hinext : i.val + 1 < n)
    (hnext : IsLoop (rankTwoToeplitz a) ⟨i.val + 1, hinext⟩)
    (hi : ¬IsLoop (rankTwoToeplitz a) i) (j : Fin n) :
    ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔ j = i := by
  constructor
  · intro hij
    rcases lt_trichotomy j i with hji | rfl | hijlt
    · have hiprev : 0 < i.val := by omega
      let prev : Fin n := ⟨i.val - 1, by omega⟩
      have hprevparallel : ColumnsPositivelyParallel (rankTwoToeplitz a) i prev :=
        (rankTwoToeplitz_parallelClasses_ordConnected a hA hi).out
          hij (columnsPositivelyParallel_refl _ _)
          ⟨by change j.val ≤ prev.val; simp [prev]; omega,
            by change prev.val ≤ i.val; simp [prev]⟩
      have hlocal := rankTwoToeplitz_not_parallel_previous_of_next_loop
        a i hiprev hinext hnext hi
      exact False.elim (hlocal (by
        have := columnsPositivelyParallel_symm hprevparallel
        simpa [prev] using this))
    · rfl
    · have hjnonloop := columnsPositivelyParallel_not_isLoop_right hij hi
      let next : Fin n := ⟨i.val + 1, hinext⟩
      have hnextnonloop : ¬IsLoop (rankTwoToeplitz a) next :=
        (rankTwoToeplitz_nonloop_ordConnected a hA).out hi hjnonloop
          ⟨by change i.val ≤ next.val; simp [next],
            by change next.val ≤ j.val; simp [next]; omega⟩
      exact False.elim (hnextnonloop (by simpa [next] using hnext))
  · rintro rfl
    exact columnsPositivelyParallel_refl _ _

/-- A nonzero maximal minor supplies two ordered nonloop columns in different parallel classes. -/
theorem hasFullRowRank_exists_nonparallel_columns
    {A : Matrix (Fin 2) (Fin n) ℝ} (hA : HasFullRowRank A) :
    ∃ i j : Fin n, i < j ∧ ¬IsLoop A i ∧ ¬IsLoop A j ∧
      ¬ColumnsPositivelyParallel A i j := by
  obtain ⟨cols, hcols⟩ := hA
  let i := cols 0
  let j := cols 1
  have hij : i < j := cols.strictMono (by decide)
  have hminor : orderedPairMinor A i j ≠ 0 := by
    rw [orderedMinor_two] at hcols
    simpa [i, j, allRows, orderedPairMinor] using hcols
  have hi : ¬IsLoop A i := by
    intro hloop
    rw [isLoop_iff_entry_eq_zero] at hloop
    apply hminor
    simp [orderedPairMinor, hloop]
  have hj : ¬IsLoop A j := by
    intro hloop
    rw [isLoop_iff_entry_eq_zero] at hloop
    apply hminor
    simp [orderedPairMinor, hloop]
  refine ⟨i, j, hij, hi, hj, ?_⟩
  rintro ⟨c, -, hcol⟩
  exact hminor (orderedPairMinor_eq_zero_of_column_eq_smul A i j c hcol)

/-- The complete collection of matrix-level necessary properties in the rank-two
classification. -/
structure RankTwoNecessaryProperties (a : Fin (n + 1) → ℝ) : Prop where
  coefficientSupport_ordConnected : Set.OrdConnected {k | 0 < a k}
  nonloop_ordConnected : Set.OrdConnected {j | ¬IsLoop (rankTwoToeplitz a) j}
  projective_mono : ∀ {i j : Fin n}, i ≤ j →
    ¬IsLoop (rankTwoToeplitz a) i → ¬IsLoop (rankTwoToeplitz a) j →
    rankTwoProjectiveParameterWithTop a i ≤ rankTwoProjectiveParameterWithTop a j
  parallelClass_ordConnected : ∀ {i : Fin n}, ¬IsLoop (rankTwoToeplitz a) i →
    Set.OrdConnected {j | ColumnsPositivelyParallel (rankTwoToeplitz a) i j}
  initialClass_singleton : ∀ (i : Fin n) (hi0 : 0 < i.val),
    IsLoop (rankTwoToeplitz a) ⟨i.val - 1, by omega⟩ →
    ¬IsLoop (rankTwoToeplitz a) i → ∀ j,
    ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔ j = i
  terminalClass_singleton : ∀ (i : Fin n) (hinext : i.val + 1 < n),
    IsLoop (rankTwoToeplitz a) ⟨i.val + 1, hinext⟩ →
    ¬IsLoop (rankTwoToeplitz a) i → ∀ j,
    ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔ j = i
  two_distinct_classes : ∃ i j : Fin n, i < j ∧
    ¬IsLoop (rankTwoToeplitz a) i ∧ ¬IsLoop (rankTwoToeplitz a) j ∧
    ¬ColumnsPositivelyParallel (rankTwoToeplitz a) i j

/-- Matrix-level necessity in the rank-two classification theorem. -/
theorem rankTwo_classification_necessity
    (a : Fin (n + 1) → ℝ) (hTN : TotallyNonnegative (rankTwoToeplitz a))
    (hfull : HasFullRowRank (rankTwoToeplitz a)) :
    RankTwoNecessaryProperties a where
  coefficientSupport_ordConnected := rankTwoToeplitz_positiveSupport_ordConnected a hTN
  nonloop_ordConnected := rankTwoToeplitz_nonloop_ordConnected a hTN
  projective_mono hij hi hj := rankTwoProjectiveParameterWithTop_mono a hTN hij hi hj
  parallelClass_ordConnected hi := rankTwoToeplitz_parallelClasses_ordConnected a hTN hi
  initialClass_singleton i hi0 hprev hi j :=
    rankTwoToeplitz_initial_parallel_class_singleton a hTN i hi0 hprev hi j
  terminalClass_singleton i hinext hnext hi j :=
    rankTwoToeplitz_terminal_parallel_class_singleton a hTN i hinext hnext hi j
  two_distinct_classes := hasFullRowRank_exists_nonparallel_columns hfull

/-! ## Realization in the positive finite-projective chart -/

/-- Data for a loop-free full-rank rank-two realization.  Weak monotonicity permits arbitrary
consecutive parallel blocks, while the distinguished strict comparison certifies full row rank. -/
structure PositiveRankTwoDatum (n : ℕ) where
  /-- Prescribed finite projective parameters. -/
  parameter : Fin n → ℝ
  /-- All prescribed parameters lie in the positive finite chart. -/
  parameter_pos : ∀ j, 0 < parameter j
  /-- The prescribed parameters respect the column order. -/
  parameter_mono : Monotone parameter
  /-- Left column of a strict comparison. -/
  left : Fin n
  /-- Right column of a strict comparison. -/
  right : Fin n
  left_lt_right : left < right
  parameter_lt : parameter left < parameter right

namespace PositiveRankTwoDatum

/-- Extend a finite parameter sequence to natural indices, using the harmless value one outside
its range. -/
noncomputable def extendedParameter (D : PositiveRankTwoDatum n) (k : ℕ) : ℝ :=
  if h : k < n then D.parameter ⟨k, h⟩ else 1

/-- Positive Toeplitz coefficients recovered multiplicatively from the prescribed projective
parameters, starting with coefficient one. -/
noncomputable def coefficients (D : PositiveRankTwoDatum n) (k : Fin (n + 1)) : ℝ :=
  ∏ t ∈ Finset.range k.val, (D.extendedParameter t)⁻¹

@[simp]
theorem coefficients_zero (D : PositiveRankTwoDatum n) : D.coefficients 0 = 1 := by
  simp [coefficients]

/-- The recovered coefficients satisfy the defining Toeplitz overlap recurrence. -/
theorem coefficients_succ (D : PositiveRankTwoDatum n) (j : Fin n) :
    D.coefficients j.succ = D.coefficients j.castSucc / D.parameter j := by
  classical
  rw [coefficients, coefficients]
  simp only [Fin.val_succ, Fin.val_castSucc, Finset.prod_range_succ]
  have hext : D.extendedParameter j.val = D.parameter j := by
    simp [extendedParameter, j.isLt]
  rw [hext]
  simp [div_eq_mul_inv]

/-- Every recovered coefficient is strictly positive. -/
theorem coefficients_pos (D : PositiveRankTwoDatum n) (k : Fin (n + 1)) :
    0 < D.coefficients k := by
  classical
  rw [coefficients]
  apply Finset.prod_pos
  intro t ht
  have htn : t < n := by
    have htk : t < k.val := Finset.mem_range.mp ht
    omega
  rw [show D.extendedParameter t = D.parameter ⟨t, htn⟩ by
    simp [extendedParameter, htn]]
  exact inv_pos.mpr (D.parameter_pos _)

/-- The lower entry of each realized column is its upper entry times the prescribed parameter. -/
theorem coefficients_castSucc_eq_succ_mul (D : PositiveRankTwoDatum n) (j : Fin n) :
    D.coefficients j.castSucc = D.coefficients j.succ * D.parameter j := by
  rw [D.coefficients_succ]
  field_simp [D.parameter_pos j |>.ne']

/-- Every entry of the realized Toeplitz matrix is positive. -/
theorem realization_entry_pos (D : PositiveRankTwoDatum n) (i : Fin 2) (j : Fin n) :
    0 < rankTwoToeplitz D.coefficients i j := by
  fin_cases i
  · simpa using D.coefficients_pos j.succ
  · simpa using D.coefficients_pos j.castSucc

/-- The realized pair minors have the prescribed projective factorization. -/
theorem realization_pairMinor (D : PositiveRankTwoDatum n) (i j : Fin n) :
    orderedPairMinor (rankTwoToeplitz D.coefficients) i j =
      D.coefficients i.succ * D.coefficients j.succ *
        (D.parameter j - D.parameter i) := by
  rw [orderedPairMinor_rankTwoToeplitz, D.coefficients_castSucc_eq_succ_mul,
    D.coefficients_castSucc_eq_succ_mul]
  ring

/-- The recovered matrix is totally nonnegative in every minor order. -/
theorem realization_totallyNonnegative (D : PositiveRankTwoDatum n) :
    TotallyNonnegative (rankTwoToeplitz D.coefficients) := by
  intro k rows cols
  cases k with
  | zero => simp
  | succ k =>
      cases k with
      | zero =>
          rw [orderedMinor_one]
          exact (D.realization_entry_pos (rows 0) (cols 0)).le
      | succ k =>
          cases k with
          | zero =>
              have hrows : rows 0 < rows 1 := rows.strictMono (by decide)
              have hcols : cols 0 < cols 1 := cols.strictMono (by decide)
              have hrow₀ : rows 0 = 0 := by
                apply Fin.ext
                omega
              have hrow₁ : rows 1 = 1 := by
                apply Fin.ext
                omega
              rw [orderedMinor_two, hrow₀, hrow₁]
              change 0 ≤ orderedPairMinor (rankTwoToeplitz D.coefficients) (cols 0) (cols 1)
              rw [D.realization_pairMinor]
              exact mul_nonneg
                (mul_nonneg (D.coefficients_pos _).le (D.coefficients_pos _).le)
                (sub_nonneg.mpr (D.parameter_mono hcols.le))
          | succ k =>
              exfalso
              have hcard := Fintype.card_le_of_injective rows rows.injective
              simp only [Fintype.card_fin] at hcard
              omega

/-- The prescribed strict comparison gives a nonzero maximal minor and hence full row rank. -/
theorem realization_hasFullRowRank (D : PositiveRankTwoDatum n) :
    HasFullRowRank (rankTwoToeplitz D.coefficients) := by
  refine ⟨pairOrderEmbedding D.left D.right D.left_lt_right, ?_⟩
  rw [orderedMinor_two]
  change orderedPairMinor (rankTwoToeplitz D.coefficients) D.left D.right ≠ 0
  rw [D.realization_pairMinor]
  exact mul_ne_zero (mul_ne_zero (D.coefficients_pos _).ne' (D.coefficients_pos _).ne')
    (sub_ne_zero.mpr D.parameter_lt.ne')

/-- Positive parallelism in the realization is exactly equality of prescribed parameters. -/
theorem realization_columnsPositivelyParallel_iff (D : PositiveRankTwoDatum n) (i j : Fin n) :
    ColumnsPositivelyParallel (rankTwoToeplitz D.coefficients) i j ↔
      D.parameter i = D.parameter j := by
  constructor
  · rintro ⟨c, hc, hcol⟩
    have hzero := orderedPairMinor_eq_zero_of_column_eq_smul
      (rankTwoToeplitz D.coefficients) i j c hcol
    rw [D.realization_pairMinor] at hzero
    have hprod : D.coefficients i.succ * D.coefficients j.succ ≠ 0 :=
      mul_ne_zero (D.coefficients_pos _).ne' (D.coefficients_pos _).ne'
    have hsub : D.parameter j - D.parameter i = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hprod
    exact (sub_eq_zero.mp hsub).symm
  · intro hij
    have hminor : orderedPairMinor (rankTwoToeplitz D.coefficients) i j = 0 := by
      rw [D.realization_pairMinor, hij, sub_self, mul_zero]
    exact columnsPositivelyParallel_of_orderedPairMinor_eq_zero
      (i := i) (j := j) (fun r s ↦ (D.realization_entry_pos r s).le)
      (by
        rw [rankTwoToeplitz_isLoop_iff]
        exact fun h ↦ (D.coefficients_pos _).ne' h.1)
      (by
        rw [rankTwoToeplitz_isLoop_iff]
        exact fun h ↦ (D.coefficients_pos _).ne' h.1)
      hminor

/-- The realization theorem for arbitrary positive finite-projective data. -/
theorem exists_realization (D : PositiveRankTwoDatum n) :
    ∃ a : Fin (n + 1) → ℝ,
      (∀ k, 0 < a k) ∧
      TotallyNonnegative (rankTwoToeplitz a) ∧
      HasFullRowRank (rankTwoToeplitz a) ∧
      (∀ i j, ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔
        D.parameter i = D.parameter j) := by
  refine ⟨D.coefficients, D.coefficients_pos, D.realization_totallyNonnegative,
    D.realization_hasFullRowRank, ?_⟩
  exact D.realization_columnsPositivelyParallel_iff

end PositiveRankTwoDatum

/-- A composition of the ordered ground set, encoded by a surjective monotone block map.  The
condition `2 ≤ blocks` is precisely the full-rank restriction. -/
structure PositiveRankTwoCompositionDatum (n blocks : ℕ) where
  block : Fin n → Fin blocks
  block_mono : Monotone block
  block_surjective : Function.Surjective block
  two_le_blocks : 2 ≤ blocks

namespace PositiveRankTwoCompositionDatum

/-- Block zero, available because the datum has at least two blocks. -/
def zeroBlock (D : PositiveRankTwoCompositionDatum n blocks) : Fin blocks :=
  ⟨0, by have := D.two_le_blocks; omega⟩

/-- Block one, available because the datum has at least two blocks. -/
def oneBlock (D : PositiveRankTwoCompositionDatum n blocks) : Fin blocks :=
  ⟨1, by have := D.two_le_blocks; omega⟩

/-- The first column in block zero. -/
noncomputable def leftRepresentative (D : PositiveRankTwoCompositionDatum n blocks) : Fin n :=
  Classical.choose (D.block_surjective D.zeroBlock)

/-- A column in block one. -/
noncomputable def rightRepresentative (D : PositiveRankTwoCompositionDatum n blocks) : Fin n :=
  Classical.choose (D.block_surjective D.oneBlock)

@[simp]
theorem block_leftRepresentative (D : PositiveRankTwoCompositionDatum n blocks) :
    D.block D.leftRepresentative = D.zeroBlock :=
  Classical.choose_spec (D.block_surjective D.zeroBlock)

@[simp]
theorem block_rightRepresentative (D : PositiveRankTwoCompositionDatum n blocks) :
    D.block D.rightRepresentative = D.oneBlock :=
  Classical.choose_spec (D.block_surjective D.oneBlock)

/-- Assigning parameter `block + 1` turns a composition into positive projective data. -/
noncomputable def toPositiveRankTwoDatum
    (D : PositiveRankTwoCompositionDatum n blocks) : PositiveRankTwoDatum n where
  parameter j := (D.block j).val + 1
  parameter_pos j := by positivity
  parameter_mono := by
    intro i j hij
    have hblock := D.block_mono hij
    norm_num only [Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.add_le_add_right hblock 1
  left := D.leftRepresentative
  right := D.rightRepresentative
  left_lt_right := by
    by_contra hnot
    have hblock := D.block_mono (not_lt.mp hnot)
    rw [D.block_rightRepresentative, D.block_leftRepresentative] at hblock
    change (1 : ℕ) ≤ 0 at hblock
    omega
  parameter_lt := by
    simp [zeroBlock, oneBlock]

@[simp]
theorem toPositiveRankTwoDatum_parameter
    (D : PositiveRankTwoCompositionDatum n blocks) (j : Fin n) :
    D.toPositiveRankTwoDatum.parameter j = (D.block j).val + 1 :=
  rfl

theorem toPositiveRankTwoDatum_parameter_eq_iff
    (D : PositiveRankTwoCompositionDatum n blocks) (i j : Fin n) :
    D.toPositiveRankTwoDatum.parameter i = D.toPositiveRankTwoDatum.parameter j ↔
      D.block i = D.block j := by
  simp only [toPositiveRankTwoDatum_parameter]
  constructor
  · intro h
    apply Fin.ext
    have hnat : (D.block i).val + 1 = (D.block j).val + 1 := by
      exact_mod_cast h
    exact Nat.add_right_cancel hnat
  · intro h
    rw [h]

/-- Every ordered composition with at least two blocks has a positive full-row-rank totally
nonnegative Toeplitz realization whose parallel classes are exactly its fibers. -/
theorem exists_realization (D : PositiveRankTwoCompositionDatum n blocks) :
    ∃ a : Fin (n + 1) → ℝ,
      (∀ k, 0 < a k) ∧
      TotallyNonnegative (rankTwoToeplitz a) ∧
      HasFullRowRank (rankTwoToeplitz a) ∧
      (∀ i j, ColumnsPositivelyParallel (rankTwoToeplitz a) i j ↔
        D.block i = D.block j) := by
  obtain ⟨a, ha, hTN, hfull, hparallel⟩ := D.toPositiveRankTwoDatum.exists_realization
  refine ⟨a, ha, hTN, hfull, ?_⟩
  intro i j
  rw [hparallel, D.toPositiveRankTwoDatum_parameter_eq_iff]

end PositiveRankTwoCompositionDatum

end ToeplitzPositroids
