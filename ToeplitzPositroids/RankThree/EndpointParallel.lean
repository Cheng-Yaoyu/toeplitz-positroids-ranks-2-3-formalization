import ToeplitzPositroids.Matrix.ThreeRows
import ToeplitzPositroids.Matrix.Reversal
import ToeplitzPositroids.RankThree.EndpointAlgebra
import ToeplitzPositroids.RankThree.MomentMatrix
import ToeplitzPositroids.RankThree.OrderTwo
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Endpoint parallel classes in rank three

This file develops the structural part of Theorem 10 and Lemma 11 of
*Toeplitz Positroids in Ranks Two and Three*.  Since the project represents a
simplified configuration directly through raw matrix columns, endpoint classes
are stated in terms of loops and positive parallelism rather than through a
separate quotient type.
-/

namespace ToeplitzPositroids

open Matrix
open RankThree

section GeneralThreeRowMatrix

variable {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}

/-- Coefficient values agree when their finite indices have the same natural
value. -/
theorem coefficient_eq_of_val {m : ℕ} (a : Fin m → ℝ) {i j : Fin m}
    (hij : i.val = j.val) : a i = a j :=
  congrArg a (Fin.ext hij)

/-- A rank-three Toeplitz column at natural position `p`, with all coefficient
indices written as natural offsets. -/
theorem rankThreeToeplitz_natColumn {a : Fin (n + 2) → ℝ} (p : ℕ) (hp : p < n) :
    (rankThreeToeplitz a).col ⟨p, hp⟩ =
      ![a ⟨p + 2, by omega⟩, a ⟨p + 1, by omega⟩, a ⟨p, by omega⟩] := by
  funext i
  fin_cases i <;> rfl

/-- Positive parallelism between Toeplitz columns gives the three coefficient
equalities obtained by reading the column equality row by row. -/
theorem rankThreeToeplitz_columnsPositivelyParallel_entries
    {a : Fin (n + 2) → ℝ} {i j : Fin n}
    (hij : ColumnsPositivelyParallel (rankThreeToeplitz a) i j) :
    ∃ lambda : ℝ, 0 < lambda ∧
      a j.succ.succ = lambda * a i.succ.succ ∧
      a j.succ.castSucc = lambda * a i.succ.castSucc ∧
      a j.castSucc.castSucc = lambda * a i.castSucc.castSucc := by
  rcases hij with ⟨lambda, hlambda, hcol⟩
  refine ⟨lambda, hlambda, ?_, ?_, ?_⟩
  · simpa [Matrix.col_apply] using congrFun hcol (0 : Fin 3)
  · simpa [Matrix.col_apply] using congrFun hcol (1 : Fin 3)
  · simpa [Matrix.col_apply] using congrFun hcol (2 : Fin 3)

/-- In a `TN₂` three-row matrix, every nonloop column lying between two
parallel nonloop columns belongs to the same parallel class. -/
theorem columnsParallel_interval_of_tnUpTo_two (hA : TNUpTo A 2)
    {i j k : Fin n} (hij : i ≤ k) (hkj : k ≤ j) (hparallel : ColumnsParallel A i j)
    (hk : ¬IsLoop A k) :
    ColumnsParallel A i k ∧ ColumnsParallel A k j := by
  have hi : ¬IsLoop A i := hparallel.1
  have hj : ¬IsLoop A j := (columnsParallel_symm hparallel).1
  rcases hij.eq_or_lt with rfl | hik
  · exact ⟨columnsParallel_refl hi, hparallel⟩
  rcases hkj.eq_or_lt with rfl | hkj
  · exact ⟨hparallel, columnsParallel_refl hj⟩
  have hmomentIJ : momentU (A.col i) = momentU (A.col j) :=
    (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA
      (hik.trans hkj) hi hj).2 hparallel.2
  have hmomentIK : momentU (A.col i) ≤ momentU (A.col k) :=
    momentU_col_le_of_tnUpTo_two hA hik hi hk
  have hmomentKJ : momentU (A.col k) ≤ momentU (A.col j) :=
    momentU_col_le_of_tnUpTo_two hA hkj hk hj
  have hikEq : momentU (A.col i) = momentU (A.col k) := by
    apply le_antisymm hmomentIK
    simpa [hmomentIJ] using hmomentKJ
  have hkjEq : momentU (A.col k) = momentU (A.col j) := by
    apply le_antisymm hmomentKJ
    simpa [hmomentIJ] using hmomentIK
  exact
    ⟨⟨hi, (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA hik hi hk).1 hikEq⟩,
      ⟨hk, (momentU_cols_eq_iff_positivelyParallel_of_tnUpTo_two hA hkj hk hj).1 hkjEq⟩⟩

/-- Consequently, a positive-parallel fiber among the nonloop columns is an
ordinary interval in the column order. -/
theorem columnsPositivelyParallel_interval_of_tnUpTo_two (hA : TNUpTo A 2)
    {i j k : Fin n} (hik : i < k) (hkj : k < j)
    (hi : ¬IsLoop A i) (hk : ¬IsLoop A k)
    (hparallel : ColumnsPositivelyParallel A i j) :
    ColumnsPositivelyParallel A i k ∧ ColumnsPositivelyParallel A k j := by
  exact (columnsParallel_interval_of_tnUpTo_two hA hik.le hkj.le
    ⟨hi, hparallel⟩ hk).imp And.right And.right

end GeneralThreeRowMatrix

section GeometricRun

variable {n : ℕ}

/-- A block of at least two mutually positive-parallel Toeplitz columns forces
the entire overlapping coefficient segment to be geometric.  The segment has
`L + 2` coefficients because a three-row column exposes three consecutive
coefficients. -/
theorem rankThreeToeplitz_geometricSegment_of_parallelBlock
    {a : Fin (n + 2) → ℝ} {p L : ℕ} (hL : 2 ≤ L) (hbound : p + L ≤ n)
    (hparallel : ∀ t : Fin L,
      ColumnsPositivelyParallel (rankThreeToeplitz a)
        ⟨p, by omega⟩ ⟨p + t, by omega⟩) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ t : Fin (L + 2),
        a ⟨p + t, by omega⟩ = a ⟨p, by omega⟩ * lambda ^ (t : ℕ) := by
  let first : Fin n := ⟨p, by omega⟩
  let second : Fin n := ⟨p + 1, by omega⟩
  let b : Fin (L + 2) → ℝ := fun t ↦ a ⟨p + t, by omega⟩
  obtain ⟨lambda, hlambda, htop, hmiddle, hbottom⟩ :=
    rankThreeToeplitz_columnsPositivelyParallel_entries
      (hparallel ⟨1, by omega⟩)
  have hlambda₀ : b 1 = lambda * b 0 := by
    simpa [b, first, second] using hbottom
  have hlambda₁ : b ⟨2, by omega⟩ = lambda * b 1 := by
    change a ⟨p + 2, by omega⟩ = lambda * a ⟨p + 1, by omega⟩
    exact hmiddle
  have hstep : ∀ s : Fin (L + 1),
      b ⟨s + 1, by omega⟩ = lambda * b ⟨s, by omega⟩ := by
    intro s
    by_cases hs : (s : ℕ) < L
    · let current : Fin n := ⟨p + s, by omega⟩
      obtain ⟨mu, hmu, htopCurrent, hmiddleCurrent, hbottomCurrent⟩ :=
        rankThreeToeplitz_columnsPositivelyParallel_entries
          (hparallel ⟨s, hs⟩)
      have hcurrent₀ : b ⟨s, by omega⟩ = mu * b 0 := by
        simpa [b, first, current] using hbottomCurrent
      have hcurrent₁ : b ⟨s + 1, by omega⟩ = mu * b 1 := by
        simpa [b, first, current] using hmiddleCurrent
      rw [hcurrent₁, hlambda₀, hcurrent₀]
      ring
    · have hsEq : (s : ℕ) = L := by omega
      let last : Fin n := ⟨p + (L - 1), by omega⟩
      obtain ⟨mu, hmu, htopLast, hmiddleLast, hbottomLast⟩ :=
        rankThreeToeplitz_columnsPositivelyParallel_entries
          (hparallel ⟨L - 1, by omega⟩)
      have hlast₁ : b ⟨L, by omega⟩ = mu * b 1 := by
        change a ⟨p + L, by omega⟩ = mu * a ⟨p + 1, by omega⟩
        convert hmiddleLast using 1
        congr 1
        apply Fin.ext
        simp
        omega
      have hlast₂ : b ⟨L + 1, by omega⟩ = mu * b ⟨2, by omega⟩ := by
        change a ⟨p + (L + 1), by omega⟩ = mu * a ⟨p + 2, by omega⟩
        convert htopLast using 1
        · congr 1
          apply Fin.ext
          simp
          omega
      have hsFin : s = ⟨L, by omega⟩ := by
        apply Fin.ext
        exact hsEq
      rw [hsFin]
      change b ⟨L + 1, by omega⟩ = lambda * b ⟨L, by omega⟩
      rw [hlast₂, hlambda₁, hlast₁]
      ring
  refine ⟨lambda, hlambda, ?_⟩
  intro t
  change b t = b 0 * lambda ^ (t : ℕ)
  have hformula : ∀ k : ℕ, (hk : k < L + 2) →
      b ⟨k, hk⟩ = b 0 * lambda ^ k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k < L + 1 := by omega
        rw [hstep ⟨k, hk'⟩, ih (by omega), pow_succ]
        ring
  exact hformula t (by omega)

/-- Under `TN₂`, parallel endpoints and the absence of loops inside a block
already supply the whole parallel block required by the geometric-segment
lemma. -/
theorem rankThreeToeplitz_geometricSegment_of_parallelEndpoints
    {a : Fin (n + 2) → ℝ} {p L : ℕ} (hL : 2 ≤ L) (hbound : p + L ≤ n)
    (hTwo : TNUpTo (rankThreeToeplitz a) 2)
    (hendpoints : ColumnsParallel (rankThreeToeplitz a)
      ⟨p, by omega⟩ ⟨p + L - 1, by omega⟩)
    (hnonloop : ∀ t : Fin L,
      ¬IsLoop (rankThreeToeplitz a) ⟨p + t, by omega⟩) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ t : Fin (L + 2),
        a ⟨p + t, by omega⟩ = a ⟨p, by omega⟩ * lambda ^ (t : ℕ) := by
  apply rankThreeToeplitz_geometricSegment_of_parallelBlock hL hbound
  intro t
  have hbetween := columnsParallel_interval_of_tnUpTo_two hTwo
    (A := rankThreeToeplitz a)
    (i := (⟨p, by omega⟩ : Fin n))
    (j := (⟨p + L - 1, by omega⟩ : Fin n))
    (k := (⟨p + t, by omega⟩ : Fin n))
    (by apply Fin.mk_le_mk.mpr; omega) (by apply Fin.mk_le_mk.mpr; omega)
    hendpoints (hnonloop t)
  exact hbetween.1.2

end GeometricRun

section InternalTrap

variable {L : ℕ} {c lambda e f : ℝ}

/-- Once the geometric-run calculation has produced the two end inequalities,
nonnegativity of the trap minor contradicts strict maximality at both ends.
This is the logical core of the internal-parallel-class exclusion. -/
theorem internalParallelTrap_contradiction
    (hc : 0 < c) (he : e * lambda ≤ 1) (hf : f ≤ lambda ^ (L + 2))
    (hminor : 0 ≤ (internalParallelTrapMatrix c lambda e f L).det)
    (hleftMaximal : e * lambda ≠ 1)
    (hrightMaximal : f ≠ lambda ^ (L + 2)) : False := by
  have hnonpos : (internalParallelTrapMatrix c lambda e f L).det ≤ 0 :=
    internalParallelTrapMatrix_det_nonpos hc.le he hf
  have hzero : (internalParallelTrapMatrix c lambda e f L).det = 0 :=
    le_antisymm hnonpos hminor
  rw [internalParallelTrapMatrix_det] at hzero
  rcases mul_eq_zero.mp hzero with hproduct | hleft
  · rcases mul_eq_zero.mp hproduct with hcCube | hright
    · exact hc.ne' (eq_zero_of_pow_eq_zero hcCube)
    · apply hrightMaximal
      linarith
  · apply hleftMaximal
    linarith

/-- The internal-parallel trap with all geometric and endpoint data derived
from an actual maximal parallel block.  In particular, this theorem does not
assume a geometric run or either maximality factor. -/
theorem rankThreeToeplitz_no_internal_maximalParallelBlock
    {n p L : ℕ} {a : Fin (n + 2) → ℝ}
    (hp : 1 ≤ p) (hL : 2 ≤ L) (hbound : p + L < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hendpoints : ColumnsParallel (rankThreeToeplitz a)
      ⟨p, by omega⟩ ⟨p + L - 1, by omega⟩)
    (hnonloop : ∀ t : Fin L,
      ¬IsLoop (rankThreeToeplitz a) ⟨p + t, by omega⟩)
    (hleftMaximal : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨p - 1, by omega⟩ ⟨p, by omega⟩)
    (hrightMaximal : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨p + L - 1, by omega⟩ ⟨p + L, by omega⟩) : False := by
  let first : Fin n := ⟨p, by omega⟩
  let last : Fin n := ⟨p + L - 1, by omega⟩
  let left : Fin n := ⟨p - 1, by omega⟩
  let right : Fin n := ⟨p + L, by omega⟩
  have hTwo : TNUpTo (rankThreeToeplitz a) 2 := hA.tnUpTo 2
  have hblock : ∀ t : Fin L,
      ColumnsPositivelyParallel (rankThreeToeplitz a) first ⟨p + t, by omega⟩ := by
    intro t
    have hbetween := columnsParallel_interval_of_tnUpTo_two hTwo
      (A := rankThreeToeplitz a) (i := first) (j := last)
      (k := (⟨p + t, by omega⟩ : Fin n))
      (by apply Fin.mk_le_mk.mpr; change p ≤ p + t; omega)
      (by apply Fin.mk_le_mk.mpr; change p + t ≤ p + L - 1; omega)
      (by simpa [first, last] using hendpoints) (hnonloop t)
    exact hbetween.1.2
  obtain ⟨lambda, hlambda, hgeom⟩ :=
    rankThreeToeplitz_geometricSegment_of_parallelBlock (a := a) (p := p) (L := L)
      hL (by omega) (by
      simpa [first] using hblock)
  let c : ℝ := a ⟨p, by omega⟩
  have hgeomAt : ∀ (t : ℕ) (ht : t < L + 2),
      a ⟨p + t, by omega⟩ = c * lambda ^ t := by
    intro t ht
    simpa [c] using hgeom ⟨t, ht⟩
  have hcne : c ≠ 0 := by
    intro hc
    have h₀ := hgeomAt 0 (by omega)
    have h₁ := hgeomAt 1 (by omega)
    have h₂ := hgeomAt 2 (by omega)
    have hfloop : IsLoop (rankThreeToeplitz a) first := by
      rw [IsLoop, rankThreeToeplitz_natColumn p (by omega)]
      funext i
      fin_cases i
      · change a ⟨p + 2, by omega⟩ = 0
        rw [h₂, hc]
        simp
      · change a ⟨p + 1, by omega⟩ = 0
        rw [h₁, hc]
        simp
      · change a ⟨p, by omega⟩ = 0
        simpa [c] using hc
    exact (hnonloop ⟨0, by omega⟩) (by simpa [first] using hfloop)
  have hcNonneg : 0 ≤ c := by
    exact rankThreeToeplitz_coeff_nonneg (by omega) hTwo _
  have hc : 0 < c := lt_of_le_of_ne hcNonneg (Ne.symm hcne)
  let e : ℝ := a ⟨p - 1, by omega⟩ / c
  let f : ℝ := a ⟨p + L + 2, by omega⟩ / c
  have hec : a ⟨p - 1, by omega⟩ = c * e := by
    dsimp [e]
    field_simp
  have hfc : a ⟨p + L + 2, by omega⟩ = c * f := by
    dsimp [f]
    field_simp
  have hgeom₀ := hgeomAt 0 (by omega)
  have hgeom₁ := hgeomAt 1 (by omega)
  have hgeom₂ := hgeomAt 2 (by omega)
  have hgeomL := hgeomAt L (by omega)
  have hgeomL₁ := hgeomAt (L + 1) (by omega)
  have hgeomPred := hgeomAt (L - 1) (by omega)
  have hgeomL₁' :
      a ⟨p + L + 1, by omega⟩ = c * lambda ^ (L + 1) := by
    have hindex : (⟨p + L + 1, by omega⟩ : Fin (n + 2)) =
        ⟨p + (L + 1), by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex]
    exact hgeomL₁
  have hgeomPred' :
      a ⟨p + L - 1, by omega⟩ = c * lambda ^ (L - 1) := by
    have hindex : (⟨p + L - 1, by omega⟩ : Fin (n + 2)) =
        ⟨p + (L - 1), by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex]
    exact hgeomPred
  have hleftCol : (rankThreeToeplitz a).col left = ![c * lambda, c, c * e] := by
    rw [rankThreeToeplitz_natColumn (p - 1) (by omega)]
    funext i
    fin_cases i
    · change a ⟨p - 1 + 2, by omega⟩ = c * lambda
      have hindex : (⟨p - 1 + 2, by omega⟩ : Fin (n + 2)) =
          ⟨p + 1, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hindex, hgeom₁]
      simp
    · change a ⟨p - 1 + 1, by omega⟩ = c
      have hindex : (⟨p - 1 + 1, by omega⟩ : Fin (n + 2)) =
          ⟨p, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hindex]
    · change a ⟨p - 1, by omega⟩ = c * e
      exact hec
  have hfirstCol : (rankThreeToeplitz a).col first = ![c * lambda ^ 2, c * lambda, c] := by
    rw [rankThreeToeplitz_natColumn p (by omega)]
    funext i
    fin_cases i
    · change a ⟨p + 2, by omega⟩ = c * lambda ^ 2
      exact hgeom₂
    · change a ⟨p + 1, by omega⟩ = c * lambda
      rw [hgeom₁]
      simp
    · change a ⟨p, by omega⟩ = c
      rfl
  have hrightCol : (rankThreeToeplitz a).col right =
      ![c * f, c * lambda ^ (L + 1), c * lambda ^ L] := by
    rw [rankThreeToeplitz_natColumn (p + L) hbound]
    funext i
    fin_cases i
    · change a ⟨p + L + 2, by omega⟩ = c * f
      exact hfc
    · change a ⟨p + L + 1, by omega⟩ = c * lambda ^ (L + 1)
      exact hgeomL₁'
    · change a ⟨p + L, by omega⟩ = c * lambda ^ L
      exact hgeomL
  have hlastCol : (rankThreeToeplitz a).col last =
      ![c * lambda ^ (L + 1), c * lambda ^ L, c * lambda ^ (L - 1)] := by
    rw [rankThreeToeplitz_natColumn (p + L - 1) (by omega)]
    funext i
    fin_cases i
    · change a ⟨p + L - 1 + 2, by omega⟩ = c * lambda ^ (L + 1)
      have hindex : (⟨p + L - 1 + 2, by omega⟩ : Fin (n + 2)) =
          ⟨p + L + 1, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hindex, hgeomL₁']
    · change a ⟨p + L - 1 + 1, by omega⟩ = c * lambda ^ L
      have hindex : (⟨p + L - 1 + 1, by omega⟩ : Fin (n + 2)) =
          ⟨p + L, by omega⟩ := by apply Fin.ext; simp; omega
      rw [hindex, hgeomL]
    · change a ⟨p + L - 1, by omega⟩ = c * lambda ^ (L - 1)
      exact hgeomPred'
  have htrapMatrix :
      threeColumnMatrix ((rankThreeToeplitz a).col left)
          ((rankThreeToeplitz a).col first) ((rankThreeToeplitz a).col right) =
        internalParallelTrapMatrix c lambda e f L := by
    rw [hleftCol, hfirstCol, hrightCol]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [threeColumnMatrix, internalParallelTrapMatrix]
  have hlog : DiscretelyLogConcave a :=
    rankThreeToeplitz_discretelyLogConcave (by omega) hTwo
  have hlogLeftRaw := hlog ⟨p - 1, by omega⟩
  have hlogLeftIndex₀ : (⟨p - 1, by omega⟩ : Fin n).castSucc.castSucc =
      (⟨p - 1, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; rfl
  have hlogLeftIndex₁ : (⟨p - 1, by omega⟩ : Fin n).succ.castSucc =
      (⟨p, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; simp; omega
  have hlogLeftIndex₂ : (⟨p - 1, by omega⟩ : Fin n).succ.succ =
      (⟨p + 1, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; simp; omega
  have hlogLeft :
      a ⟨p - 1, by omega⟩ * a ⟨p + 1, by omega⟩ ≤
        a ⟨p, by omega⟩ * a ⟨p, by omega⟩ := by
    rw [hlogLeftIndex₀, hlogLeftIndex₁, hlogLeftIndex₂] at hlogLeftRaw
    exact hlogLeftRaw
  have heLambda : e * lambda ≤ 1 := by
    apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hc)
    calc
      c ^ 2 * (e * lambda) = (c * e) * (c * lambda) := by ring
      _ = a ⟨p - 1, by omega⟩ * a ⟨p + 1, by omega⟩ := by
        rw [hec, hgeom₁]
        simp
      _ ≤ a ⟨p, by omega⟩ * a ⟨p, by omega⟩ := hlogLeft
      _ = c ^ 2 * 1 := by simp [c, pow_two]
  have hlogRightRaw := hlog ⟨p + L, by omega⟩
  have hlogRightIndex₀ : (⟨p + L, hbound⟩ : Fin n).castSucc.castSucc =
      (⟨p + L, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; rfl
  have hlogRightIndex₁ : (⟨p + L, hbound⟩ : Fin n).succ.castSucc =
      (⟨p + L + 1, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; rfl
  have hlogRightIndex₂ : (⟨p + L, hbound⟩ : Fin n).succ.succ =
      (⟨p + L + 2, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; rfl
  have hlogRight :
      a ⟨p + L, by omega⟩ * a ⟨p + L + 2, by omega⟩ ≤
        a ⟨p + L + 1, by omega⟩ * a ⟨p + L + 1, by omega⟩ := by
    rw [hlogRightIndex₀, hlogRightIndex₁, hlogRightIndex₂] at hlogRightRaw
    exact hlogRightRaw
  have hfactorPos : 0 < c ^ 2 * lambda ^ L :=
    mul_pos (sq_pos_of_pos hc) (pow_pos hlambda _)
  have hfLambda : f ≤ lambda ^ (L + 2) := by
    apply le_of_mul_le_mul_left ?_ hfactorPos
    calc
      (c ^ 2 * lambda ^ L) * f =
          a ⟨p + L, by omega⟩ * a ⟨p + L + 2, by omega⟩ := by
        rw [hgeomL, hfc]
        ring
      _ ≤ a ⟨p + L + 1, by omega⟩ * a ⟨p + L + 1, by omega⟩ := hlogRight
      _ = (c ^ 2 * lambda ^ L) * lambda ^ (L + 2) := by
        rw [hgeomL₁']
        simp [pow_succ]
        ring
  have hleftFirst : left < first := by simp [left, first]; omega
  have hfirstRight : first < right := by simp [first, right]; omega
  have hminor : 0 ≤ (internalParallelTrapMatrix c lambda e f L).det := by
    have hm := hA.orderedMinor_nonneg (allRows 3)
      (selectedTripleEmbedding left first right hleftFirst hfirstRight)
    rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det
      (rankThreeToeplitz a) hleftFirst hfirstRight, htrapMatrix] at hm
    exact hm
  have hleftFactor : e * lambda ≠ 1 := by
    intro heq
    apply hleftMaximal
    refine ⟨lambda, hlambda, ?_⟩
    rw [hleftCol, hfirstCol]
    funext i
    fin_cases i
    · change c * lambda ^ 2 = lambda * (c * lambda)
      ring
    · change c * lambda = lambda * c
      ring
    · calc
        c = (e * lambda) * c := by rw [heq, one_mul]
        _ = lambda * (c * e) := by ring
  have hrightFactor : f ≠ lambda ^ (L + 2) := by
    intro hfeq
    apply hrightMaximal
    refine ⟨lambda, hlambda, ?_⟩
    rw [hlastCol, hrightCol]
    funext i
    fin_cases i
    · change c * f = lambda * (c * lambda ^ (L + 1))
      rw [hfeq, pow_succ]
      ring
    · change c * lambda ^ (L + 1) = lambda * (c * lambda ^ L)
      rw [pow_succ]
      ring
    · change c * lambda ^ L = lambda * (c * lambda ^ (L - 1))
      have hpow : lambda ^ L = lambda * lambda ^ (L - 1) := by
        calc
          lambda ^ L = lambda ^ ((L - 1) + 1) := by congr 1; omega
          _ = lambda ^ (L - 1) * lambda := by rw [pow_succ]
          _ = lambda * lambda ^ (L - 1) := by ring
      rw [hpow]
      ring
  exact internalParallelTrap_contradiction hc heLambda hfLambda hminor
    hleftFactor hrightFactor

/-- A natural-indexed maximal nontrivial parallel block.  The block consists of
columns `p, ..., p + L - 1`; the last two fields state maximality whenever the
corresponding neighboring column exists. -/
structure IsMaximalParallelBlock {n : ℕ} (A : Matrix (Fin 3) (Fin n) ℝ)
    (p L : ℕ) : Prop where
  two_le : 2 ≤ L
  bound : p + L ≤ n
  nonloop (t : Fin L) : ¬IsLoop A ⟨p + t, by omega⟩
  parallel (t : Fin L) :
    ColumnsPositivelyParallel A ⟨p, by omega⟩ ⟨p + t, by omega⟩
  left_maximal (hp : 1 ≤ p) :
    ¬ColumnsPositivelyParallel A ⟨p - 1, by omega⟩ ⟨p, by omega⟩
  right_maximal (hright : p + L < n) :
    ¬ColumnsPositivelyParallel A
      ⟨p + L - 1, by omega⟩ ⟨p + L, hright⟩

/-- Theorem 10, in the raw-column representation: every maximal nontrivial
parallel block of a totally nonnegative rank-three Toeplitz matrix is initial
or terminal. -/
theorem rankThreeToeplitz_endpointParallel
    {n p L : ℕ} {a : Fin (n + 2) → ℝ}
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hblock : IsMaximalParallelBlock (rankThreeToeplitz a) p L) :
    p = 0 ∨ p + L = n := by
  by_contra hinterior
  have hpNe : p ≠ 0 := fun hp ↦ hinterior (Or.inl hp)
  have hrightNe : p + L ≠ n := fun hright ↦ hinterior (Or.inr hright)
  have hL : 2 ≤ L := hblock.two_le
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hpNe
  have hrightBound : p + L < n := lt_of_le_of_ne hblock.bound hrightNe
  have hnonloop : ∀ t : Fin L,
      ¬IsLoop (rankThreeToeplitz a) ⟨p + t, by omega⟩ := hblock.nonloop
  have hendpoints : ColumnsParallel (rankThreeToeplitz a)
      ⟨p, by omega⟩ ⟨p + L - 1, by omega⟩ := by
    refine ⟨hblock.nonloop ⟨0, by omega⟩, ?_⟩
    have hindex : (⟨p + (L - 1), by omega⟩ : Fin n) =
        ⟨p + L - 1, by omega⟩ := by apply Fin.ext; simp; omega
    rw [← hindex]
    exact hblock.parallel ⟨L - 1, by omega⟩
  exact rankThreeToeplitz_no_internal_maximalParallelBlock hp hL
    hrightBound hA hendpoints hnonloop (hblock.left_maximal hp)
    (hblock.right_maximal hrightBound)

/-- The full-row-rank formulation of the endpoint-parallel theorem used in the
paper.  The endpoint conclusion itself is stronger and does not need the rank
hypothesis. -/
theorem rankThreeToeplitz_endpointParallel_of_fullRowRank
    {n p L : ℕ} {a : Fin (n + 2) → ℝ}
    (hA : HasFullRowRank (rankThreeToeplitz a) ∧
      TotallyNonnegative (rankThreeToeplitz a))
    (hblock : IsMaximalParallelBlock (rankThreeToeplitz a) p L) :
    p = 0 ∨ p + L = n :=
  rankThreeToeplitz_endpointParallel hA.2 hblock

end InternalTrap

section Reversal

/-- Reversing both axes of a selected minor is the same as selecting the
reverse-complementary rows and columns; the two determinant signs cancel. -/
theorem orderedMinor_submatrix_rev {R : Type*} [CommRing R] {m n k : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (rows : Fin k ↪o Fin m)
    (cols : Fin k ↪o Fin n) :
    orderedMinor (A.submatrix Fin.rev Fin.rev) rows cols =
      orderedMinor A (reverseOrderEmbedding rows) (reverseOrderEmbedding cols) := by
  exact orderedMinor_reverseMatrix A rows cols

/-- Simultaneous reversal of rows and columns preserves total nonnegativity. -/
theorem TotallyNonnegative.submatrix_rev {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : TotallyNonnegative A) :
    TotallyNonnegative (A.submatrix Fin.rev Fin.rev) := by
  exact hA.reverseMatrix

/-- Simultaneous reversal also preserves full row rank. -/
theorem HasFullRowRank.submatrix_rev {m n : ℕ}
    {A : Matrix (Fin m) (Fin n) ℝ} (hA : HasFullRowRank A) :
    HasFullRowRank (A.submatrix Fin.rev Fin.rev) := by
  exact (hasFullRowRank_reverseMatrix_iff A).2 hA

/-- A reversed column is a loop exactly when the corresponding original column
is a loop. -/
theorem isLoop_submatrix_rev_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (j : Fin n) :
    IsLoop (A.submatrix Fin.rev Fin.rev) j ↔ IsLoop A j.rev := by
  rw [isLoop_iff_entry_eq_zero, isLoop_iff_entry_eq_zero]
  constructor
  · intro h i
    simpa using h i.rev
  · intro h i
    simpa using h i.rev

/-- Positive parallelism is transported by simultaneous reversal. -/
theorem columnsPositivelyParallel_submatrix_rev_iff {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (i j : Fin n) :
    ColumnsPositivelyParallel (A.submatrix Fin.rev Fin.rev) i j ↔
      ColumnsPositivelyParallel A i.rev j.rev := by
  constructor
  · rintro ⟨c, hc, hcol⟩
    refine ⟨c, hc, ?_⟩
    funext r
    have hr := congrFun hcol r.rev
    simpa [Matrix.col_apply] using hr
  · rintro ⟨c, hc, hcol⟩
    refine ⟨c, hc, ?_⟩
    funext r
    have hr := congrFun hcol r.rev
    simpa [Matrix.col_apply] using hr

end Reversal

section EndpointProtection

variable {n : ℕ}

/-- A three-column determinant vanishes when its first two columns are positive
scalar multiples. -/
theorem threeColumnMatrix_det_eq_zero_of_positivelyParallel_left
    {u v w : Column} (huv : PositivelyParallel u v) :
    (threeColumnMatrix u v w).det = 0 := by
  rcases huv with ⟨lambda, hlambda, huv⟩
  have h₀ := congrFun huv (0 : Fin 3)
  have h₁ := congrFun huv (1 : Fin 3)
  have h₂ := congrFun huv (2 : Fin 3)
  rw [Matrix.det_fin_three]
  change
    u 0 * v 1 * w 2 - u 0 * w 1 * v 2 - v 0 * u 1 * w 2 +
          v 0 * w 1 * u 2 + w 0 * u 1 * v 2 - w 0 * v 1 * u 2 = 0
  simp only [Pi.smul_apply, smul_eq_mul] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]
  ring

/-- A three-column determinant also vanishes when its last two columns are
positive scalar multiples. -/
theorem threeColumnMatrix_det_eq_zero_of_positivelyParallel_right
    {u v w : Column} (hvw : PositivelyParallel v w) :
    (threeColumnMatrix u v w).det = 0 := by
  rcases hvw with ⟨lambda, hlambda, hvw⟩
  have h₀ := congrFun hvw (0 : Fin 3)
  have h₁ := congrFun hvw (1 : Fin 3)
  have h₂ := congrFun hvw (2 : Fin 3)
  rw [Matrix.det_fin_three]
  change
    u 0 * v 1 * w 2 - u 0 * w 1 * v 2 - v 0 * u 1 * w 2 +
          v 0 * w 1 * u 2 + w 0 * u 1 * v 2 - w 0 * v 1 * u 2 = 0
  simp only [Pi.smul_apply, smul_eq_mul] at h₀ h₁ h₂
  rw [h₀, h₁, h₂]
  ring

/-- The increasing embedding selecting three consecutive columns. -/
def consecutiveTripleEmbedding (p : ℕ) (hbound : p + 2 < n) : Fin 3 ↪o Fin n :=
  selectedTripleEmbedding ⟨p, by omega⟩ ⟨p + 1, by omega⟩ ⟨p + 2, hbound⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- The increasing embedding selecting columns `p - 2`, `p - 1`, and `p`. -/
def terminalTripleEmbedding (p : ℕ) (hp : 2 ≤ p) (hpBound : p < n) : Fin 3 ↪o Fin n :=
  selectedTripleEmbedding ⟨p - 2, by omega⟩ ⟨p - 1, by omega⟩ ⟨p, hpBound⟩
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))

/-- A boundary-form selected triple has determinant `b0³`. -/
theorem selectedTriple_det_eq_leftBoundaryTriple
    {A : Matrix (Fin 3) (Fin n) ℝ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) {b0 b1 b2 : ℝ}
    (hmatrix : threeColumnMatrix (A.col i) (A.col j) (A.col k) =
      leftBoundaryTriple b0 b1 b2) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) = b0 ^ 3 := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det A hij hjk,
    hmatrix, leftBoundaryTriple_det]

/-- An endpoint-protection-form selected triple has the determinant from
formula (6.5). -/
theorem selectedTriple_det_eq_endpointProtectionMatrix
    {A : Matrix (Fin 3) (Fin n) ℝ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) {A0 radius t w : ℝ}
    (hmatrix : threeColumnMatrix (A.col i) (A.col j) (A.col k) =
      endpointProtectionMatrix A0 radius t w) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) =
      A0 ^ 3 * (1 - radius * t) ^ 2 := by
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det A hij hjk,
    hmatrix, endpointProtectionMatrix_det]

/-- The endpoint-protection triple is strictly positive under `A0 > 0` and
`radius * t < 1`. -/
theorem selectedTriple_endpointProtection_pos
    {A : Matrix (Fin 3) (Fin n) ℝ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) {A0 radius t w : ℝ}
    (hmatrix : threeColumnMatrix (A.col i) (A.col j) (A.col k) =
      endpointProtectionMatrix A0 radius t w)
    (hA0 : 0 < A0) (hrt : radius * t < 1) :
    0 < orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) := by
  rw [selectedTriple_det_eq_endpointProtectionMatrix hij hjk hmatrix]
  exact mul_pos (pow_pos hA0 _) (pow_pos (sub_pos.mpr hrt) _)

/-- Two coefficient zeros at a left support boundary put the next three
Toeplitz columns in triangular boundary form. -/
theorem rankThreeToeplitz_leftBoundary_threeColumnMatrix
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hbound : p + 2 < n)
    (hzero₀ : a ⟨p, by omega⟩ = 0) (hzero₁ : a ⟨p + 1, by omega⟩ = 0) :
    threeColumnMatrix
        ((rankThreeToeplitz a).col ⟨p, by omega⟩)
        ((rankThreeToeplitz a).col ⟨p + 1, by omega⟩)
        ((rankThreeToeplitz a).col ⟨p + 2, hbound⟩) =
      leftBoundaryTriple (a ⟨p + 2, by omega⟩)
        (a ⟨p + 3, by omega⟩) (a ⟨p + 4, by omega⟩) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [threeColumnMatrix, leftBoundaryTriple, Matrix.col_apply,
      hzero₀, hzero₁]

/-- The first three columns following a left coefficient-support boundary have
determinant equal to the cube of the first positive coefficient. -/
theorem rankThreeToeplitz_leftBoundary_minor
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hbound : p + 2 < n)
    (hzero₀ : a ⟨p, by omega⟩ = 0) (hzero₁ : a ⟨p + 1, by omega⟩ = 0) :
    orderedMinor (rankThreeToeplitz a) (allRows 3)
        (consecutiveTripleEmbedding p hbound) =
      a ⟨p + 2, by omega⟩ ^ 3 := by
  apply selectedTriple_det_eq_leftBoundaryTriple
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
  exact rankThreeToeplitz_leftBoundary_threeColumnMatrix hbound hzero₀ hzero₁

/-- A positive first boundary coefficient makes the first three post-boundary
columns a positive basis. -/
theorem rankThreeToeplitz_leftBoundary_minor_pos
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hbound : p + 2 < n)
    (hzero₀ : a ⟨p, by omega⟩ = 0) (hzero₁ : a ⟨p + 1, by omega⟩ = 0)
    (hpositive : 0 < a ⟨p + 2, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
      (consecutiveTripleEmbedding p hbound) := by
  rw [rankThreeToeplitz_leftBoundary_minor hbound hzero₀ hzero₁]
  exact pow_pos hpositive _

/-- Therefore the first two columns after a left support boundary are not
parallel.  This is the loop-adjacent singleton assertion in Theorem 10. -/
theorem rankThreeToeplitz_leftBoundary_not_parallel
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hbound : p + 2 < n)
    (hzero₀ : a ⟨p, by omega⟩ = 0) (hzero₁ : a ⟨p + 1, by omega⟩ = 0)
    (hpositive : 0 < a ⟨p + 2, by omega⟩) :
    ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨p, by omega⟩ ⟨p + 1, by omega⟩ := by
  intro hparallel
  have hdetZero :
      orderedMinor (rankThreeToeplitz a) (allRows 3)
        (consecutiveTripleEmbedding p hbound) = 0 := by
    unfold consecutiveTripleEmbedding
    rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
    exact threeColumnMatrix_det_eq_zero_of_positivelyParallel_left hparallel
  have hdetPos := rankThreeToeplitz_leftBoundary_minor_pos
    hbound hzero₀ hzero₁ hpositive
  linarith

/-- A loop immediately before column `p` forces the two lower coefficients of
column `p` to vanish. -/
theorem rankThreeToeplitz_zeros_of_loop_predecessor
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 1 ≤ p) (hpBound : p < n)
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p - 1, by omega⟩) :
    a ⟨p, by omega⟩ = 0 ∧ a ⟨p + 1, by omega⟩ = 0 := by
  have hentries := isLoop_iff_entry_eq_zero.mp hloop
  constructor
  · have h := hentries (1 : Fin 3)
    rw [rankThreeToeplitz_row_one] at h
    convert h using 1
    congr 1
    apply Fin.ext
    simp
    omega
  · have h := hentries (0 : Fin 3)
    rw [rankThreeToeplitz_row_zero] at h
    convert h using 1
    congr 1
    apply Fin.ext
    simp
    omega

/-- If column `p` is the first nonloop after a loop, its top coefficient is
strictly positive under order-one nonnegativity. -/
theorem rankThreeToeplitz_top_coefficient_pos_after_loop
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 1 ≤ p) (hpBound : p < n)
    (hA : TNUpTo (rankThreeToeplitz a) 2)
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p - 1, by omega⟩)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, hpBound⟩) :
    0 < a ⟨p + 2, by omega⟩ := by
  rcases rankThreeToeplitz_zeros_of_loop_predecessor hp hpBound hloop with
    ⟨hzero₀, hzero₁⟩
  have hnonneg : 0 ≤ a ⟨p + 2, by omega⟩ :=
    rankThreeToeplitz_coeff_nonneg (by omega) hA _
  have hne : a ⟨p + 2, by omega⟩ ≠ 0 := by
    intro hzero₂
    apply hnonloop
    rw [isLoop_iff_entry_eq_zero]
    intro i
    fin_cases i
    · simpa using hzero₂
    · simpa using hzero₁
    · simpa using hzero₀
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Loop-adjacent endpoint protection: provided three columns remain, the first
nonloop after a loop starts a singleton parallel class and the first three
post-boundary columns form a positive basis. -/
theorem rankThreeToeplitz_loopAdjacent_endpointProtection
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 1 ≤ p) (hbound : p + 2 < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p - 1, by omega⟩)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
        (consecutiveTripleEmbedding p hbound) ∧
      ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
        ⟨p, by omega⟩ ⟨p + 1, by omega⟩ := by
  rcases rankThreeToeplitz_zeros_of_loop_predecessor hp (by omega) hloop with
    ⟨hzero₀, hzero₁⟩
  have hpositive := rankThreeToeplitz_top_coefficient_pos_after_loop
    hp (by omega) (hA.tnUpTo 2) hloop hnonloop
  exact ⟨rankThreeToeplitz_leftBoundary_minor_pos
      hbound hzero₀ hzero₁ hpositive,
    rankThreeToeplitz_leftBoundary_not_parallel
      hbound hzero₀ hzero₁ hpositive⟩

/-- Full row rank leaves at least three columns at or after the first nonloop
column.  Otherwise every maximal minor would contain a loop. -/
theorem two_successors_of_fullRowRank_of_initial_loops
    {A : Matrix (Fin 3) (Fin n) ℝ} {p : ℕ} (hpBound : p < n)
    (hfull : HasFullRowRank A)
    (hloops : ∀ j : Fin n, j.val < p → IsLoop A j) : p + 2 < n := by
  by_contra hbound
  obtain ⟨cols, hcols⟩ := hfull
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  have hfirst : (cols 0).val < p := by
    by_contra hfirst
    have hpFirst : p ≤ (cols 0).val := by omega
    have hlastBound : (cols 2).val < n := (cols 2).isLt
    omega
  have hloop := hloops (cols 0) hfirst
  have hzeroEntries := isLoop_iff_entry_eq_zero.mp hloop
  apply hcols
  rw [orderedMinor]
  apply Matrix.det_eq_zero_of_column_eq_zero 0
  intro i
  exact hzeroEntries (allRows 3 i)

/-- The full-rank version of left loop-adjacent endpoint protection does not
need a separate column-count hypothesis. -/
theorem rankThreeToeplitz_initialLoops_endpointProtection
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 1 ≤ p) (hpBound : p < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (hloops : ∀ j : Fin n, j.val < p → IsLoop (rankThreeToeplitz a) j)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, hpBound⟩) :
    ∃ hbound : p + 2 < n,
      0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
          (consecutiveTripleEmbedding p hbound) ∧
        ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
          ⟨p, by omega⟩ ⟨p + 1, by omega⟩ := by
  have hbound := two_successors_of_fullRowRank_of_initial_loops hpBound hfull hloops
  refine ⟨hbound, ?_⟩
  exact rankThreeToeplitz_loopAdjacent_endpointProtection hp hbound hA
    (hloops ⟨p - 1, by omega⟩ (by change p - 1 < p; omega)) hnonloop

/-- The lower-triangular boundary matrix obtained by reversing both orders in
`leftBoundaryTriple`. -/
def rightBoundaryTriple (b0 b1 b2 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![b0, 0, 0; b1, b0, 0; b2, b1, b0]

/-- The explicit terminal boundary matrix is the simultaneous reversal of the
initial boundary matrix. -/
theorem rightBoundaryTriple_eq_reverse (b0 b1 b2 : ℝ) :
    rightBoundaryTriple b0 b1 b2 = reverseThree (leftBoundaryTriple b0 b1 b2) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The terminal boundary determinant is again `b0³`; the two reversal signs
cancel. -/
theorem rightBoundaryTriple_det (b0 b1 b2 : ℝ) :
    (rightBoundaryTriple b0 b1 b2).det = b0 ^ 3 := by
  rw [rightBoundaryTriple_eq_reverse, reverseThree_det, leftBoundaryTriple_det]

/-- Two zero coefficients at a right support boundary put the preceding three
columns in lower-triangular boundary form. -/
theorem rankThreeToeplitz_rightBoundary_threeColumnMatrix
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 2 ≤ p) (hpBound : p < n)
    (hzero₁ : a ⟨p + 1, by omega⟩ = 0) (hzero₂ : a ⟨p + 2, by omega⟩ = 0) :
    threeColumnMatrix
        ((rankThreeToeplitz a).col ⟨p - 2, by omega⟩)
        ((rankThreeToeplitz a).col ⟨p - 1, by omega⟩)
        ((rankThreeToeplitz a).col ⟨p, hpBound⟩) =
      rightBoundaryTriple (a ⟨p, by omega⟩)
        (a ⟨p - 1, by omega⟩) (a ⟨p - 2, by omega⟩) := by
  rw [rankThreeToeplitz_natColumn (p - 2) (by omega),
    rankThreeToeplitz_natColumn (p - 1) (by omega),
    rankThreeToeplitz_natColumn p hpBound]
  ext i j
  fin_cases i <;> fin_cases j
  · change a ⟨p - 2 + 2, by omega⟩ = a ⟨p, by omega⟩
    have hindex : (⟨p - 2 + 2, by omega⟩ : Fin (n + 2)) =
        ⟨p, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hindex]
  · change a ⟨p - 1 + 2, by omega⟩ = 0
    have hindex : (⟨p - 1 + 2, by omega⟩ : Fin (n + 2)) =
        ⟨p + 1, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hindex, hzero₁]
  · change a ⟨p + 2, by omega⟩ = 0
    exact hzero₂
  · change a ⟨p - 2 + 1, by omega⟩ = a ⟨p - 1, by omega⟩
    have hindex : (⟨p - 2 + 1, by omega⟩ : Fin (n + 2)) =
        ⟨p - 1, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hindex]
  · change a ⟨p - 1 + 1, by omega⟩ = a ⟨p, by omega⟩
    have hindex : (⟨p - 1 + 1, by omega⟩ : Fin (n + 2)) =
        ⟨p, by omega⟩ := by apply Fin.ext; simp; omega
    rw [hindex]
  · change a ⟨p + 1, by omega⟩ = 0
    exact hzero₁
  · rfl
  · rfl
  · rfl

/-- The last three columns before a right support boundary have determinant
equal to the cube of the last positive coefficient. -/
theorem rankThreeToeplitz_rightBoundary_minor
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 2 ≤ p) (hpBound : p < n)
    (hzero₁ : a ⟨p + 1, by omega⟩ = 0) (hzero₂ : a ⟨p + 2, by omega⟩ = 0) :
    orderedMinor (rankThreeToeplitz a) (allRows 3)
        (terminalTripleEmbedding p hp hpBound) =
      a ⟨p, by omega⟩ ^ 3 := by
  unfold terminalTripleEmbedding
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
  rw [rankThreeToeplitz_rightBoundary_threeColumnMatrix hp hpBound hzero₁ hzero₂,
    rightBoundaryTriple_det]

/-- A positive final boundary coefficient makes the last three pre-boundary
columns a positive basis. -/
theorem rankThreeToeplitz_rightBoundary_minor_pos
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 2 ≤ p) (hpBound : p < n)
    (hzero₁ : a ⟨p + 1, by omega⟩ = 0) (hzero₂ : a ⟨p + 2, by omega⟩ = 0)
    (hpositive : 0 < a ⟨p, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
      (terminalTripleEmbedding p hp hpBound) := by
  rw [rankThreeToeplitz_rightBoundary_minor hp hpBound hzero₁ hzero₂]
  exact pow_pos hpositive _

/-- The final two columns before a right support boundary are not parallel. -/
theorem rankThreeToeplitz_rightBoundary_not_parallel
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 2 ≤ p) (hpBound : p < n)
    (hzero₁ : a ⟨p + 1, by omega⟩ = 0) (hzero₂ : a ⟨p + 2, by omega⟩ = 0)
    (hpositive : 0 < a ⟨p, by omega⟩) :
    ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨p - 1, by omega⟩ ⟨p, hpBound⟩ := by
  intro hparallel
  have hdetZero :
      orderedMinor (rankThreeToeplitz a) (allRows 3)
        (terminalTripleEmbedding p hp hpBound) = 0 := by
    unfold terminalTripleEmbedding
    rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
    exact threeColumnMatrix_det_eq_zero_of_positivelyParallel_right hparallel
  have hdetPos := rankThreeToeplitz_rightBoundary_minor_pos
    hp hpBound hzero₁ hzero₂ hpositive
  linarith

/-- A loop immediately after column `p` forces the two upper coefficients of
column `p` to vanish. -/
theorem rankThreeToeplitz_zeros_of_loop_successor
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hpSucc : p + 1 < n)
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p + 1, hpSucc⟩) :
    a ⟨p + 1, by omega⟩ = 0 ∧ a ⟨p + 2, by omega⟩ = 0 := by
  have hentries := isLoop_iff_entry_eq_zero.mp hloop
  constructor
  · have h := hentries (2 : Fin 3)
    rw [rankThreeToeplitz_row_two] at h
    exact h
  · have h := hentries (1 : Fin 3)
    rw [rankThreeToeplitz_row_one] at h
    exact h

/-- If column `p` is the last nonloop before a loop, its bottom coefficient is
strictly positive under order-one nonnegativity. -/
theorem rankThreeToeplitz_bottom_coefficient_pos_before_loop
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hpSucc : p + 1 < n)
    (hA : TNUpTo (rankThreeToeplitz a) 2)
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p + 1, hpSucc⟩)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, by omega⟩) :
    0 < a ⟨p, by omega⟩ := by
  rcases rankThreeToeplitz_zeros_of_loop_successor hpSucc hloop with ⟨hzero₁, hzero₂⟩
  have hnonneg : 0 ≤ a ⟨p, by omega⟩ :=
    rankThreeToeplitz_coeff_nonneg (by omega) hA _
  have hne : a ⟨p, by omega⟩ ≠ 0 := by
    intro hzero₀
    apply hnonloop
    rw [isLoop_iff_entry_eq_zero]
    intro i
    fin_cases i
    · simpa using hzero₂
    · simpa using hzero₁
    · simpa using hzero₀
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Terminal loop-adjacent endpoint protection, symmetric to the left-boundary
statement. -/
theorem rankThreeToeplitz_terminalLoopAdjacent_endpointProtection
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hp : 2 ≤ p) (hpSucc : p + 1 < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hloop : IsLoop (rankThreeToeplitz a) ⟨p + 1, hpSucc⟩)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
        (terminalTripleEmbedding p hp (by omega)) ∧
      ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
        ⟨p - 1, by omega⟩ ⟨p, by omega⟩ := by
  rcases rankThreeToeplitz_zeros_of_loop_successor hpSucc hloop with ⟨hzero₁, hzero₂⟩
  have hpositive := rankThreeToeplitz_bottom_coefficient_pos_before_loop
    hpSucc (hA.tnUpTo 2) hloop hnonloop
  exact ⟨rankThreeToeplitz_rightBoundary_minor_pos
      hp (by omega) hzero₁ hzero₂ hpositive,
    rankThreeToeplitz_rightBoundary_not_parallel
      hp (by omega) hzero₁ hzero₂ hpositive⟩

/-- Full row rank leaves at least three columns at or before the last nonloop
column. -/
theorem two_predecessors_of_fullRowRank_of_terminal_loops
    {A : Matrix (Fin 3) (Fin n) ℝ} {p : ℕ}
    (hfull : HasFullRowRank A)
    (hloops : ∀ j : Fin n, p < j.val → IsLoop A j) : 2 ≤ p := by
  by_contra hp
  obtain ⟨cols, hcols⟩ := hfull
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  have hlast : p < (cols 2).val := by
    by_contra hlast
    have hlastLe : (cols 2).val ≤ p := by omega
    omega
  have hloop := hloops (cols 2) hlast
  have hzeroEntries := isLoop_iff_entry_eq_zero.mp hloop
  apply hcols
  rw [orderedMinor]
  apply Matrix.det_eq_zero_of_column_eq_zero 2
  intro i
  exact hzeroEntries (allRows 3 i)

/-- The full-rank version of terminal loop-adjacent endpoint protection. -/
theorem rankThreeToeplitz_terminalLoops_endpointProtection
    {a : Fin (n + 2) → ℝ} {p : ℕ} (hpBound : p < n) (hpSucc : p + 1 < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (hloops : ∀ j : Fin n, p < j.val → IsLoop (rankThreeToeplitz a) j)
    (hnonloop : ¬IsLoop (rankThreeToeplitz a) ⟨p, hpBound⟩) :
    ∃ hp : 2 ≤ p,
      0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
          (terminalTripleEmbedding p hp hpBound) ∧
        ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
          ⟨p - 1, by omega⟩ ⟨p, hpBound⟩ := by
  have hp := two_predecessors_of_fullRowRank_of_terminal_loops hfull hloops
  refine ⟨hp, ?_⟩
  exact rankThreeToeplitz_terminalLoopAdjacent_endpointProtection hp hpSucc hA
    (hloops ⟨p + 1, hpSucc⟩ (by change p < p + 1; omega)) hnonloop

/-- Endpoint protection at the right edge of a positive parallel pair.  The
normalized form and the strict inequality in formula (6.5) are both derived
from Toeplitz parallelism, total nonnegativity, and maximality of the pair on
the right. -/
theorem rankThreeToeplitz_parallelEndpointProtection
    {a : Fin (n + 2) → ℝ} {q : ℕ} (hq : 1 ≤ q) (hbound : q + 2 < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hA0 : 0 < a ⟨q + 2, by omega⟩)
    (hparallel : ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨q - 1, by omega⟩ ⟨q, by omega⟩)
    (hmaximal : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨q, by omega⟩ ⟨q + 1, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
      (consecutiveTripleEmbedding q hbound) := by
  obtain ⟨scale, hscale, htopRaw, hmiddleRaw, hbottomRaw⟩ :=
    rankThreeToeplitz_columnsPositivelyParallel_entries hparallel
  have htopIndex₀ : (⟨q, by omega⟩ : Fin n).succ.succ =
      (⟨q + 2, by omega⟩ : Fin (n + 2)) := by rfl
  have htopIndex₁ : (⟨q - 1, by omega⟩ : Fin n).succ.succ =
      (⟨q + 1, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; simp; omega
  have hmiddleIndex₀ : (⟨q, by omega⟩ : Fin n).succ.castSucc =
      (⟨q + 1, by omega⟩ : Fin (n + 2)) := by rfl
  have hmiddleIndex₁ : (⟨q - 1, by omega⟩ : Fin n).succ.castSucc =
      (⟨q, by omega⟩ : Fin (n + 2)) := by apply Fin.ext; simp; omega
  rw [htopIndex₀, htopIndex₁] at htopRaw
  rw [hmiddleIndex₀, hmiddleIndex₁] at hmiddleRaw
  have hcross :
      a ⟨q + 1, by omega⟩ * a ⟨q + 1, by omega⟩ =
        a ⟨q + 2, by omega⟩ * a ⟨q, by omega⟩ := by
    calc
      a ⟨q + 1, by omega⟩ * a ⟨q + 1, by omega⟩ =
          (scale * a ⟨q, by omega⟩) * a ⟨q + 1, by omega⟩ := by
            rw [hmiddleRaw]
      _ = (scale * a ⟨q + 1, by omega⟩) * a ⟨q, by omega⟩ := by ring
      _ = a ⟨q + 2, by omega⟩ * a ⟨q, by omega⟩ := by rw [htopRaw]
  let A0 : ℝ := a ⟨q + 2, by omega⟩
  let radius : ℝ := a ⟨q + 1, by omega⟩ / A0
  let t : ℝ := a ⟨q + 3, by omega⟩ / A0
  let w : ℝ := a ⟨q + 4, by omega⟩ / A0
  have hA0' : 0 < A0 := by simpa [A0] using hA0
  have hA0ne : A0 ≠ 0 := hA0'.ne'
  have hRadius : A0 * radius = a ⟨q + 1, by omega⟩ := by
    dsimp [radius]
    field_simp
  have hT : A0 * t = a ⟨q + 3, by omega⟩ := by
    dsimp [t]
    field_simp
  have hW : A0 * w = a ⟨q + 4, by omega⟩ := by
    dsimp [w]
    field_simp
  have hRadiusSq : A0 * radius ^ 2 = a ⟨q, by omega⟩ := by
    apply mul_left_cancel₀ hA0ne
    calc
      A0 * (A0 * radius ^ 2) = (A0 * radius) * (A0 * radius) := by ring
      _ = a ⟨q + 1, by omega⟩ * a ⟨q + 1, by omega⟩ := by rw [hRadius]
      _ = a ⟨q + 2, by omega⟩ * a ⟨q, by omega⟩ := hcross
      _ = A0 * a ⟨q, by omega⟩ := by rfl
  have hmatrix :
      threeColumnMatrix
          ((rankThreeToeplitz a).col ⟨q, by omega⟩)
          ((rankThreeToeplitz a).col ⟨q + 1, by omega⟩)
          ((rankThreeToeplitz a).col ⟨q + 2, hbound⟩) =
        endpointProtectionMatrix A0 radius t w := by
    rw [rankThreeToeplitz_natColumn q (by omega),
      rankThreeToeplitz_natColumn (q + 1) (by omega),
      rankThreeToeplitz_natColumn (q + 2) hbound]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [threeColumnMatrix, endpointProtectionMatrix, A0, hRadius, hT, hW, hRadiusSq]
  have hlog : DiscretelyLogConcave a :=
    rankThreeToeplitz_discretelyLogConcave (by omega) (hA.tnUpTo 2)
  have hlogRaw := hlog ⟨q + 1, by omega⟩
  have hlogIndex₀ : (⟨q + 1, by omega⟩ : Fin n).castSucc.castSucc =
      (⟨q + 1, by omega⟩ : Fin (n + 2)) := by rfl
  have hlogIndex₁ : (⟨q + 1, by omega⟩ : Fin n).succ.castSucc =
      (⟨q + 2, by omega⟩ : Fin (n + 2)) := by rfl
  have hlogIndex₂ : (⟨q + 1, by omega⟩ : Fin n).succ.succ =
      (⟨q + 3, by omega⟩ : Fin (n + 2)) := by rfl
  rw [hlogIndex₀, hlogIndex₁, hlogIndex₂] at hlogRaw
  have hrtLe : radius * t ≤ 1 := by
    apply le_of_mul_le_mul_left ?_ (sq_pos_of_pos hA0')
    calc
      A0 ^ 2 * (radius * t) = (A0 * radius) * (A0 * t) := by ring
      _ = a ⟨q + 1, by omega⟩ * a ⟨q + 3, by omega⟩ := by rw [hRadius, hT]
      _ ≤ a ⟨q + 2, by omega⟩ * a ⟨q + 2, by omega⟩ := hlogRaw
      _ = A0 ^ 2 * 1 := by simp [A0, pow_two]
  have hrtNe : radius * t ≠ 1 := by
    intro hrt
    have htNonneg : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (rankThreeToeplitz_coeff_nonneg (by omega) (hA.tnUpTo 2) _) hA0'.le
    have htNe : t ≠ 0 := by
      intro ht
      rw [ht, mul_zero] at hrt
      norm_num at hrt
    have ht : 0 < t := lt_of_le_of_ne htNonneg (Ne.symm htNe)
    apply hmaximal
    refine ⟨t, ht, ?_⟩
    rw [rankThreeToeplitz_natColumn (q + 1) (by omega),
      rankThreeToeplitz_natColumn q (by omega)]
    funext i
    fin_cases i
    · change a ⟨q + 3, by omega⟩ = t * a ⟨q + 2, by omega⟩
      rw [← hT]
      ring
    · change a ⟨q + 2, by omega⟩ = t * a ⟨q + 1, by omega⟩
      rw [← hRadius]
      change A0 = t * (A0 * radius)
      calc
        A0 = (radius * t) * A0 := by rw [hrt, one_mul]
        _ = t * (A0 * radius) := by ring
    · change a ⟨q + 1, by omega⟩ = t * a ⟨q, by omega⟩
      rw [← hRadius, ← hRadiusSq]
      calc
        A0 * radius = (radius * t) * (A0 * radius) := by rw [hrt, one_mul]
        _ = t * (A0 * radius ^ 2) := by ring
  have hrt : radius * t < 1 := lt_of_le_of_ne hrtLe hrtNe
  exact selectedTriple_endpointProtection_pos
    (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
    hmatrix hA0' hrt

/-- Full row rank leaves two columns after a nontrivial initial parallel block.
Otherwise every maximal minor would contain two columns of that block. -/
theorem two_successors_of_fullRowRank_of_initial_parallelBlock
    {A : Matrix (Fin 3) (Fin n) ℝ} {L : ℕ}
    (hfull : HasFullRowRank A) (hblock : IsMaximalParallelBlock A 0 L) :
    L + 1 < n := by
  by_contra hcount
  obtain ⟨cols, hcolsNonzero⟩ := hfull
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  have hcol₁ : (cols 1).val < L := by
    by_contra hcol₁
    have hLcol₁ : L ≤ (cols 1).val := by omega
    have hcol₂Bound := (cols 2).isLt
    omega
  have hcol₀ : (cols 0).val < L := lt_trans h₀₁ hcol₁
  have hparallel₀ := hblock.parallel ⟨(cols 0).val, hcol₀⟩
  have hparallel₁ := hblock.parallel ⟨(cols 1).val, hcol₁⟩
  have hindex₀ : (⟨0 + (cols 0).val, by omega⟩ : Fin n) = cols 0 := by
    apply Fin.ext
    simp
  have hindex₁ : (⟨0 + (cols 1).val, by omega⟩ : Fin n) = cols 1 := by
    apply Fin.ext
    simp
  rw [hindex₀] at hparallel₀
  rw [hindex₁] at hparallel₁
  have hparallel₀₁ : ColumnsPositivelyParallel A (cols 0) (cols 1) :=
    columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hparallel₀) hparallel₁
  have hcolsEq : cols = selectedTripleEmbedding (cols 0) (cols 1) (cols 2) h₀₁ h₁₂ := by
    ext i
    fin_cases i <;> rfl
  apply hcolsNonzero
  rw [hcolsEq, orderedMinor_selectedTriple_eq_threeColumnMatrix_det A h₀₁ h₁₂]
  exact threeColumnMatrix_det_eq_zero_of_positivelyParallel_left hparallel₀₁

/-- Lemma 11 for a nontrivial initial parallel class: full row rank supplies
the next two columns, and the first three distinct columns at the endpoint form
a positive basis. -/
theorem rankThreeToeplitz_initialParallel_endpointProtection
    {a : Fin (n + 2) → ℝ} {L : ℕ}
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (hblock : IsMaximalParallelBlock (rankThreeToeplitz a) 0 L) :
    ∃ hbound : (L - 1) + 2 < n,
      0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
        (consecutiveTripleEmbedding (L - 1) hbound) := by
  have hL : 2 ≤ L := hblock.two_le
  have hcount : L + 1 < n :=
    two_successors_of_fullRowRank_of_initial_parallelBlock hfull hblock
  obtain ⟨lambda, hlambda, hgeom⟩ :=
    rankThreeToeplitz_geometricSegment_of_parallelBlock
      (a := a) (p := 0) (L := L) hL hblock.bound hblock.parallel
  let c : ℝ := a ⟨0, by omega⟩
  have hcne : c ≠ 0 := by
    intro hc
    have h₀ := hgeom (0 : Fin (L + 2))
    have h₁ := hgeom (1 : Fin (L + 2))
    have h₂ := hgeom ⟨2, by omega⟩
    have hc' : a ⟨0, by omega⟩ = 0 := by simpa [c] using hc
    rw [hc'] at h₁ h₂
    apply hblock.nonloop ⟨0, by omega⟩
    have hindex : (⟨0 + (⟨0, by omega⟩ : Fin L), by omega⟩ : Fin n) = ⟨0, by omega⟩ := by
      apply Fin.ext
      simp
    rw [hindex]
    rw [IsLoop, rankThreeToeplitz_natColumn 0 (by omega)]
    funext i
    fin_cases i
    · change a ⟨2, by omega⟩ = 0
      simpa using h₂
    · change a ⟨1, by omega⟩ = 0
      simpa using h₁
    · change a ⟨0, by omega⟩ = 0
      exact hc'
  have hcNonneg : 0 ≤ c :=
    rankThreeToeplitz_coeff_nonneg (by omega) (hA.tnUpTo 2) _
  have hc : 0 < c := lt_of_le_of_ne hcNonneg (Ne.symm hcne)
  have hA0 : 0 < a ⟨(L - 1) + 2, by omega⟩ := by
    have hlast := hgeom ⟨L + 1, by omega⟩
    have hindex : (⟨(L - 1) + 2, by omega⟩ : Fin (n + 2)) =
        ⟨0 + (L + 1), by omega⟩ := by apply Fin.ext; simp; omega
    rw [hindex, hlast]
    simpa [c] using mul_pos hc (pow_pos hlambda (L + 1))
  have hprev := hblock.parallel ⟨L - 2, by omega⟩
  have hlast := hblock.parallel ⟨L - 1, by omega⟩
  have hpair : ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨(L - 1) - 1, by omega⟩ ⟨L - 1, by omega⟩ := by
    have hpair' := columnsPositivelyParallel_trans
      (columnsPositivelyParallel_symm hprev) hlast
    simpa only [Nat.zero_add] using hpair'
  have hright : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨L - 1, by omega⟩ ⟨(L - 1) + 1, by omega⟩ := by
    have hmax := hblock.right_maximal (by omega)
    have hindex : (⟨(L - 1) + 1, by omega⟩ : Fin n) = ⟨L, by omega⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex]
    simpa only [Nat.zero_add] using hmax
  have hbound : (L - 1) + 2 < n := by omega
  refine ⟨hbound, ?_⟩
  exact rankThreeToeplitz_parallelEndpointProtection (by omega) hbound hA
    hA0 hpair hright

/-- The terminal counterpart of parallel endpoint protection, obtained by
reversing both matrix orders. -/
theorem rankThreeToeplitz_terminalParallel_endpointProtection
    {a : Fin (n + 2) → ℝ} {r : ℕ} (hr : 2 ≤ r) (hrSucc : r + 1 < n)
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hbottom : 0 < a ⟨r, by omega⟩)
    (hparallel : ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨r, by omega⟩ ⟨r + 1, hrSucc⟩)
    (hmaximal : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨r - 1, by omega⟩ ⟨r, by omega⟩) :
    0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
      (terminalTripleEmbedding r hr (by omega)) := by
  let arev : Fin (n + 2) → ℝ := a ∘ Fin.rev
  let q : ℕ := n - 1 - r
  have hq : 1 ≤ q := by simp [q]; omega
  have hqBound : q + 2 < n := by simp [q]; omega
  have hArev : TotallyNonnegative (rankThreeToeplitz arev) := by
    rw [← rankThreeToeplitz_submatrix_rev]
    exact hA.submatrix_rev
  have hqRev : (⟨q, by omega⟩ : Fin n).rev = ⟨r, by omega⟩ := by
    apply Fin.ext
    simp [q]
    omega
  have hqPredRev : (⟨q - 1, by omega⟩ : Fin n).rev = ⟨r + 1, hrSucc⟩ := by
    apply Fin.ext
    simp [q]
    omega
  have hqSuccRev : (⟨q + 1, by omega⟩ : Fin n).rev = ⟨r - 1, by omega⟩ := by
    apply Fin.ext
    simp [q]
    omega
  have hparallelMapped : ColumnsPositivelyParallel (rankThreeToeplitz a)
      (⟨q - 1, by omega⟩ : Fin n).rev (⟨q, by omega⟩ : Fin n).rev := by
    rw [hqPredRev, hqRev]
    exact columnsPositivelyParallel_symm hparallel
  have hparallelRev : ColumnsPositivelyParallel (rankThreeToeplitz arev)
      ⟨q - 1, by omega⟩ ⟨q, by omega⟩ := by
    rw [← rankThreeToeplitz_submatrix_rev]
    exact (columnsPositivelyParallel_submatrix_rev_iff
      (rankThreeToeplitz a) _ _).2 hparallelMapped
  have hmaximalMapped : ¬ColumnsPositivelyParallel (rankThreeToeplitz a)
      (⟨q, by omega⟩ : Fin n).rev (⟨q + 1, by omega⟩ : Fin n).rev := by
    rw [hqRev, hqSuccRev]
    intro h
    exact hmaximal (columnsPositivelyParallel_symm h)
  have hmaximalRev : ¬ColumnsPositivelyParallel (rankThreeToeplitz arev)
      ⟨q, by omega⟩ ⟨q + 1, by omega⟩ := by
    rw [← rankThreeToeplitz_submatrix_rev]
    simpa only [columnsPositivelyParallel_submatrix_rev_iff] using hmaximalMapped
  have hindex : (⟨q + 2, by omega⟩ : Fin (n + 2)).rev = ⟨r, by omega⟩ := by
    apply Fin.ext
    simp [q]
    omega
  have hA0 : 0 < arev ⟨q + 2, by omega⟩ := by
    change 0 < a (⟨q + 2, by omega⟩ : Fin (n + 2)).rev
    rw [hindex]
    exact hbottom
  have hposRev := rankThreeToeplitz_parallelEndpointProtection hq hqBound
    hArev hA0 hparallelRev hmaximalRev
  rw [← rankThreeToeplitz_submatrix_rev, orderedMinor_submatrix_rev] at hposRev
  have hrows : reverseOrderEmbedding (allRows 3) = allRows 3 := by
    apply RelEmbedding.ext
    intro i
    simp [allRows]
  have hcols : reverseOrderEmbedding (consecutiveTripleEmbedding q hqBound) =
      terminalTripleEmbedding r hr (by omega) := by
    apply RelEmbedding.ext
    intro i
    fin_cases i <;> apply Fin.ext <;>
      simp [consecutiveTripleEmbedding, terminalTripleEmbedding, q] <;> omega
  rw [hrows, hcols] at hposRev
  exact hposRev

/-- Full row rank leaves two columns before a nontrivial terminal parallel
block. -/
theorem two_predecessors_of_fullRowRank_of_terminal_parallelBlock
    {A : Matrix (Fin 3) (Fin n) ℝ} {p L : ℕ}
    (hfull : HasFullRowRank A) (hblock : IsMaximalParallelBlock A p L)
    (hterminal : p + L = n) : 2 ≤ p := by
  by_contra hp
  obtain ⟨cols, hcolsNonzero⟩ := hfull
  have h₀₁ : cols 0 < cols 1 := cols.strictMono (by decide)
  have h₁₂ : cols 1 < cols 2 := cols.strictMono (by decide)
  have hpCol₁ : p ≤ (cols 1).val := by
    by_contra hpCol₁
    omega
  have hpCol₂ : p ≤ (cols 2).val := hpCol₁.trans h₁₂.le
  have hcol₁ : (cols 1).val - p < L := by
    have := (cols 1).isLt
    omega
  have hcol₂ : (cols 2).val - p < L := by
    have := (cols 2).isLt
    omega
  have hparallel₁ := hblock.parallel ⟨(cols 1).val - p, hcol₁⟩
  have hparallel₂ := hblock.parallel ⟨(cols 2).val - p, hcol₂⟩
  have hindex₁ : (⟨p + ((cols 1).val - p), by omega⟩ : Fin n) = cols 1 := by
    apply Fin.ext
    simp
    omega
  have hindex₂ : (⟨p + ((cols 2).val - p), by omega⟩ : Fin n) = cols 2 := by
    apply Fin.ext
    simp
    omega
  rw [hindex₁] at hparallel₁
  rw [hindex₂] at hparallel₂
  have hparallel₁₂ : ColumnsPositivelyParallel A (cols 1) (cols 2) :=
    columnsPositivelyParallel_trans (columnsPositivelyParallel_symm hparallel₁) hparallel₂
  have hcolsEq : cols = selectedTripleEmbedding (cols 0) (cols 1) (cols 2) h₀₁ h₁₂ := by
    ext i
    fin_cases i <;> rfl
  apply hcolsNonzero
  rw [hcolsEq, orderedMinor_selectedTriple_eq_threeColumnMatrix_det A h₀₁ h₁₂]
  exact threeColumnMatrix_det_eq_zero_of_positivelyParallel_right hparallel₁₂

/-- Lemma 11 for a nontrivial terminal parallel class. -/
theorem rankThreeToeplitz_terminalParallelBlock_endpointProtection
    {a : Fin (n + 2) → ℝ} {p L : ℕ}
    (hA : TotallyNonnegative (rankThreeToeplitz a))
    (hfull : HasFullRowRank (rankThreeToeplitz a))
    (hblock : IsMaximalParallelBlock (rankThreeToeplitz a) p L)
    (hterminal : p + L = n) :
    ∃ hp : 2 ≤ p,
      ∃ hpBound : p < n,
        0 < orderedMinor (rankThreeToeplitz a) (allRows 3)
          (terminalTripleEmbedding p hp hpBound) := by
  have hL : 2 ≤ L := hblock.two_le
  have hp : 2 ≤ p :=
    two_predecessors_of_fullRowRank_of_terminal_parallelBlock hfull hblock hterminal
  have hpSucc : p + 1 < n := by omega
  obtain ⟨lambda, hlambda, hgeom⟩ :=
    rankThreeToeplitz_geometricSegment_of_parallelBlock
      (a := a) (p := p) (L := L) hL hblock.bound hblock.parallel
  let c : ℝ := a ⟨p, by omega⟩
  have hcne : c ≠ 0 := by
    intro hc
    have h₀ := hgeom (0 : Fin (L + 2))
    have h₁ := hgeom (1 : Fin (L + 2))
    have h₂ := hgeom ⟨2, by omega⟩
    have hc' : a ⟨p, by omega⟩ = 0 := by simpa [c] using hc
    rw [hc'] at h₁ h₂
    apply hblock.nonloop ⟨0, by omega⟩
    have hindex : (⟨p + (⟨0, by omega⟩ : Fin L), by omega⟩ : Fin n) =
        ⟨p, by omega⟩ := by apply Fin.ext; simp
    rw [hindex, IsLoop, rankThreeToeplitz_natColumn p (by omega)]
    funext i
    fin_cases i
    · change a ⟨p + 2, by omega⟩ = 0
      simpa using h₂
    · change a ⟨p + 1, by omega⟩ = 0
      simpa using h₁
    · exact hc'
  have hcNonneg : 0 ≤ c :=
    rankThreeToeplitz_coeff_nonneg (by omega) (hA.tnUpTo 2) _
  have hc : 0 < c := lt_of_le_of_ne hcNonneg (Ne.symm hcne)
  have hpair : ColumnsPositivelyParallel (rankThreeToeplitz a)
      ⟨p, by omega⟩ ⟨p + 1, hpSucc⟩ := by
    have hp1 := hblock.parallel ⟨1, by omega⟩
    simpa using hp1
  have hmax := hblock.left_maximal (by omega : 1 ≤ p)
  refine ⟨hp, by omega, ?_⟩
  exact rankThreeToeplitz_terminalParallel_endpointProtection hp hpSucc hA hc
    hpair hmax

end EndpointProtection

end ToeplitzPositroids
