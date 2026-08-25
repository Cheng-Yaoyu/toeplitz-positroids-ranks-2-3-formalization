import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.SuccPred.Archimedean
import Mathlib.Tactic

/-!
# Discrete convex chains

This file develops the elementary affine geometry used in the rank-three
classification.  A finite chain is represented by coordinate functions on
natural-number indices together with an upper bound on the indices under
consideration.  This convention avoids coercion overhead while retaining exact
statements for every finite initial segment.

The central result says that, when the first coordinates are strictly
increasing, nonnegativity of every ordered oriented area is equivalent to
monotonicity of the consecutive edge slopes.
-/

namespace ToeplitzPositroids

section DiscreteConvexChain

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The slope of the chord joining vertices `i` and `j`. -/
def chordSlope (x y : ℕ → K) (i j : ℕ) : K :=
  (y j - y i) / (x j - x i)

/-- The slope of the edge joining vertices `i` and `i + 1`. -/
def edgeSlope (x y : ℕ → K) (i : ℕ) : K :=
  chordSlope x y i (i + 1)

/-- Twice the signed affine area of the ordered triangle with vertices `i`, `j`, and `k`. -/
def orientedArea (x y : ℕ → K) (i j k : ℕ) : K :=
  (x j - x i) * (y k - y j) - (y j - y i) * (x k - x j)

/-- The first coordinates increase strictly on the vertices with indices below `n`. -/
def StrictlyIncreasingUpTo (x : ℕ → K) (n : ℕ) : Prop :=
  ∀ {i j : ℕ}, i < j → j < n → x i < x j

/-- The valid edge slopes form a weakly increasing sequence below vertex bound `n`. -/
def SlopesMonotoneUpTo (x y : ℕ → K) (n : ℕ) : Prop :=
  ∀ {i j : ℕ}, i ≤ j → j + 1 < n → edgeSlope x y i ≤ edgeSlope x y j

/-- Every ordered triple of vertices below `n` has nonnegative oriented area. -/
def AreasNonnegativeUpTo (x y : ℕ → K) (n : ℕ) : Prop :=
  ∀ {i j k : ℕ}, i < j → j < k → k < n → 0 ≤ orientedArea x y i j k

/-- All edge slopes from `i` through `k - 1` have the same value. -/
def SlopesConstantBetween (x y : ℕ → K) (i k : ℕ) : Prop :=
  ∀ {t : ℕ}, i ≤ t → t < k → edgeSlope x y t = edgeSlope x y i

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- A chord slope is the corresponding area-normalized determinant. -/
theorem orientedArea_eq_slopeDifference (x y : ℕ → K) {i j k : ℕ}
    (hij : x j ≠ x i) (hjk : x k ≠ x j) :
    orientedArea x y i j k =
      (x j - x i) * (x k - x j) * (chordSlope x y j k - chordSlope x y i j) := by
  simp only [orientedArea, chordSlope]
  field_simp [sub_ne_zero.mpr hij, sub_ne_zero.mpr hjk]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The consecutive-triple area is the product of the two horizontal increments and the
difference of the two consecutive edge slopes. -/
theorem orientedArea_consecutive (x y : ℕ → K) {i : ℕ}
    (h₁ : x (i + 1) ≠ x i) (h₂ : x (i + 2) ≠ x (i + 1)) :
    orientedArea x y i (i + 1) (i + 2) =
      (x (i + 1) - x i) * (x (i + 2) - x (i + 1)) *
        (edgeSlope x y (i + 1) - edgeSlope x y i) := by
  simpa [edgeSlope, Nat.add_assoc] using
    orientedArea_eq_slopeDifference x y h₁ h₂

/-- Under strict horizontal increase, a consecutive triangle has nonnegative area exactly when
its two edge slopes are ordered. -/
theorem orientedArea_consecutive_nonneg_iff (x y : ℕ → K) {i : ℕ}
    (h₁ : x i < x (i + 1)) (h₂ : x (i + 1) < x (i + 2)) :
    0 ≤ orientedArea x y i (i + 1) (i + 2) ↔
      edgeSlope x y i ≤ edgeSlope x y (i + 1) := by
  rw [orientedArea_consecutive x y (ne_of_gt h₁) (ne_of_gt h₂)]
  rw [mul_nonneg_iff_of_pos_left (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂))]
  exact sub_nonneg

/-- Under strict horizontal increase, a consecutive triangle is degenerate exactly when its two
edge slopes are equal. -/
theorem orientedArea_consecutive_eq_zero_iff (x y : ℕ → K) {i : ℕ}
    (h₁ : x i < x (i + 1)) (h₂ : x (i + 1) < x (i + 2)) :
    orientedArea x y i (i + 1) (i + 2) = 0 ↔
      edgeSlope x y i = edgeSlope x y (i + 1) := by
  rw [orientedArea_consecutive x y (ne_of_gt h₁) (ne_of_gt h₂)]
  have hp : (x (i + 1) - x i) * (x (i + 2) - x (i + 1)) ≠ 0 :=
    ne_of_gt (mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂))
  rw [mul_eq_zero]
  simp only [hp, false_or]
  constructor
  · intro h
    exact (sub_eq_zero.mp h).symm
  · intro h
    rw [h, sub_self]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Telescoping consecutive increments over a natural-number interval. -/
theorem sum_Ico_increment (f : ℕ → K) {i j : ℕ} (hij : i ≤ j) :
    ∑ t ∈ Finset.Ico i j, (f (t + 1) - f t) = f j - f i := by
  rw [Finset.sum_Ico_eq_sub _ hij, Finset.sum_range_sub, Finset.sum_range_sub]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Multiplying an edge slope by its horizontal increment recovers its vertical increment. -/
theorem horizontalIncrement_mul_edgeSlope (x y : ℕ → K) {i : ℕ}
    (hi : x i ≠ x (i + 1)) :
    (x (i + 1) - x i) * edgeSlope x y i = y (i + 1) - y i := by
  rw [edgeSlope, chordSlope]
  exact mul_div_cancel₀ _ (sub_ne_zero.mpr hi.symm)

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The vertical displacement of a chord is the sum of horizontal edge increments weighted by
their slopes. -/
theorem sum_horizontalIncrement_mul_edgeSlope (x y : ℕ → K) {i j : ℕ}
    (hij : i ≤ j) (hx : ∀ t ∈ Finset.Ico i j, x t ≠ x (t + 1)) :
    ∑ t ∈ Finset.Ico i j, (x (t + 1) - x t) * edgeSlope x y t = y j - y i := by
  calc
    ∑ t ∈ Finset.Ico i j, (x (t + 1) - x t) * edgeSlope x y t =
        ∑ t ∈ Finset.Ico i j, (y (t + 1) - y t) := by
          apply Finset.sum_congr rfl
          intro t ht
          exact horizontalIncrement_mul_edgeSlope x y (hx t ht)
    _ = y j - y i := sum_Ico_increment y hij

/-- A chord slope does not exceed the last edge slope that it crosses. -/
theorem chordSlope_le_lastEdge (x y : ℕ → K) {n i j : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) :
    chordSlope x y i j ≤ edgeSlope x y (j - 1) := by
  have hxij : 0 < x j - x i := sub_pos.mpr (hx hij hjn)
  rw [chordSlope, div_le_iff₀ hxij]
  rw [← sum_horizontalIncrement_mul_edgeSlope x y hij.le]
  · rw [← sum_Ico_increment x hij.le]
    calc
      ∑ t ∈ Finset.Ico i j, (x (t + 1) - x t) * edgeSlope x y t ≤
          ∑ t ∈ Finset.Ico i j,
            (x (t + 1) - x t) * edgeSlope x y (j - 1) := by
              apply Finset.sum_le_sum
              intro t ht
              have hit : i ≤ t := (Finset.mem_Ico.mp ht).1
              have htj : t < j := (Finset.mem_Ico.mp ht).2
              have hxt : 0 ≤ x (t + 1) - x t := by
                have ht1n : t + 1 < n :=
                  lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
                exact (sub_pos.mpr (hx (Nat.lt_succ_self t) ht1n)).le
              exact mul_le_mul_of_nonneg_left (hσ (by omega) (by omega)) hxt
      _ = edgeSlope x y (j - 1) *
          ∑ t ∈ Finset.Ico i j, (x (t + 1) - x t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            ring
  · intro t ht
    have htj : t < j := (Finset.mem_Ico.mp ht).2
    have ht1n : t + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
    exact ne_of_lt (hx (Nat.lt_succ_self t) ht1n)

/-- A chord slope is at least the first edge slope that it crosses. -/
theorem firstEdge_le_chordSlope (x y : ℕ → K) {n i j : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) :
    edgeSlope x y i ≤ chordSlope x y i j := by
  have hxij : 0 < x j - x i := sub_pos.mpr (hx hij hjn)
  rw [chordSlope, le_div_iff₀ hxij]
  rw [← sum_horizontalIncrement_mul_edgeSlope x y hij.le]
  · rw [← sum_Ico_increment x hij.le]
    calc
      edgeSlope x y i * ∑ t ∈ Finset.Ico i j, (x (t + 1) - x t) =
          ∑ t ∈ Finset.Ico i j,
            (x (t + 1) - x t) * edgeSlope x y i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro t _
              ring
      _ ≤ ∑ t ∈ Finset.Ico i j,
          (x (t + 1) - x t) * edgeSlope x y t := by
            apply Finset.sum_le_sum
            intro t ht
            have hit : i ≤ t := (Finset.mem_Ico.mp ht).1
            have htj : t < j := (Finset.mem_Ico.mp ht).2
            have hxt : 0 ≤ x (t + 1) - x t := by
              have ht1n : t + 1 < n :=
                lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
              exact (sub_pos.mpr (hx (Nat.lt_succ_self t) ht1n)).le
            exact mul_le_mul_of_nonneg_left (hσ hit (by omega)) hxt
  · intro t ht
    have htj : t < j := (Finset.mem_Ico.mp ht).2
    have ht1n : t + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
    exact ne_of_lt (hx (Nat.lt_succ_self t) ht1n)

/-- If one crossed edge has slope strictly below the last one, then the chord slope is strictly
below the last edge slope. -/
theorem chordSlope_lt_lastEdge_of_edgeSlope_lt (x y : ℕ → K) {n i j t : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) (hit : i ≤ t) (htj : t < j)
    (ht : edgeSlope x y t < edgeSlope x y (j - 1)) :
    chordSlope x y i j < edgeSlope x y (j - 1) := by
  have hxij : 0 < x j - x i := sub_pos.mpr (hx hij hjn)
  rw [chordSlope, div_lt_iff₀ hxij]
  rw [← sum_horizontalIncrement_mul_edgeSlope x y hij.le]
  · rw [← sum_Ico_increment x hij.le]
    calc
      ∑ u ∈ Finset.Ico i j, (x (u + 1) - x u) * edgeSlope x y u <
          ∑ u ∈ Finset.Ico i j,
            (x (u + 1) - x u) * edgeSlope x y (j - 1) := by
              apply Finset.sum_lt_sum
              · intro u hu
                have huj : u < j := (Finset.mem_Ico.mp hu).2
                have hu1n : u + 1 < n :=
                  lt_of_le_of_lt (Nat.succ_le_of_lt huj) hjn
                exact mul_le_mul_of_nonneg_left (hσ (by omega) (by omega))
                  (sub_nonneg.mpr (hx (Nat.lt_succ_self u) hu1n).le)
              · refine ⟨t, Finset.mem_Ico.mpr ⟨hit, htj⟩, ?_⟩
                have ht1n : t + 1 < n :=
                  lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
                exact mul_lt_mul_of_pos_left ht
                  (sub_pos.mpr (hx (Nat.lt_succ_self t) ht1n))
      _ = edgeSlope x y (j - 1) *
          ∑ u ∈ Finset.Ico i j, (x (u + 1) - x u) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
  · intro u hu
    have huj : u < j := (Finset.mem_Ico.mp hu).2
    have hu1n : u + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt huj) hjn
    exact ne_of_lt (hx (Nat.lt_succ_self u) hu1n)

/-- If one crossed edge has slope strictly above the first one, then the chord slope is strictly
above the first edge slope. -/
theorem firstEdge_lt_chordSlope_of_lt_edgeSlope (x y : ℕ → K) {n i j t : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) (hit : i ≤ t) (htj : t < j)
    (ht : edgeSlope x y i < edgeSlope x y t) :
    edgeSlope x y i < chordSlope x y i j := by
  have hxij : 0 < x j - x i := sub_pos.mpr (hx hij hjn)
  rw [chordSlope, lt_div_iff₀ hxij]
  rw [← sum_horizontalIncrement_mul_edgeSlope x y hij.le]
  · rw [← sum_Ico_increment x hij.le]
    calc
      edgeSlope x y i * ∑ u ∈ Finset.Ico i j, (x (u + 1) - x u) =
          ∑ u ∈ Finset.Ico i j,
            (x (u + 1) - x u) * edgeSlope x y i := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u _
              ring
      _ < ∑ u ∈ Finset.Ico i j,
          (x (u + 1) - x u) * edgeSlope x y u := by
            apply Finset.sum_lt_sum
            · intro u hu
              have hui : i ≤ u := (Finset.mem_Ico.mp hu).1
              have huj : u < j := (Finset.mem_Ico.mp hu).2
              have hu1n : u + 1 < n :=
                lt_of_le_of_lt (Nat.succ_le_of_lt huj) hjn
              exact mul_le_mul_of_nonneg_left (hσ hui hu1n)
                (sub_nonneg.mpr (hx (Nat.lt_succ_self u) hu1n).le)
            · refine ⟨t, Finset.mem_Ico.mpr ⟨hit, htj⟩, ?_⟩
              have ht1n : t + 1 < n :=
                lt_of_le_of_lt (Nat.succ_le_of_lt htj) hjn
              exact mul_lt_mul_of_pos_left ht
                (sub_pos.mpr (hx (Nat.lt_succ_self t) ht1n))
  · intro u hu
    have huj : u < j := (Finset.mem_Ico.mp hu).2
    have hu1n : u + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt huj) hjn
    exact ne_of_lt (hx (Nat.lt_succ_self u) hu1n)

/-- If a chord has the same slope as its last crossed edge, every crossed edge has that slope. -/
theorem edgeSlope_eq_lastEdge_of_chordSlope_eq (x y : ℕ → K) {n i j t : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) (hit : i ≤ t) (htj : t < j)
    (hchord : chordSlope x y i j = edgeSlope x y (j - 1)) :
    edgeSlope x y t = edgeSlope x y (j - 1) := by
  have hle : edgeSlope x y t ≤ edgeSlope x y (j - 1) := hσ (by omega) (by omega)
  apply le_antisymm hle
  by_contra hnot
  have hlt : edgeSlope x y t < edgeSlope x y (j - 1) := lt_of_not_ge hnot
  exact (ne_of_lt (chordSlope_lt_lastEdge_of_edgeSlope_lt x y hx hσ hij hjn hit htj hlt))
    hchord

/-- If a chord has the same slope as its first crossed edge, every crossed edge has that slope. -/
theorem edgeSlope_eq_firstEdge_of_chordSlope_eq (x y : ℕ → K) {n i j t : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjn : j < n) (hit : i ≤ t) (htj : t < j)
    (hchord : chordSlope x y i j = edgeSlope x y i) :
    edgeSlope x y t = edgeSlope x y i := by
  have hle : edgeSlope x y i ≤ edgeSlope x y t := hσ hit (by omega)
  apply le_antisymm
  · by_contra hnot
    have hlt : edgeSlope x y i < edgeSlope x y t := lt_of_not_ge hnot
    exact (ne_of_lt (firstEdge_lt_chordSlope_of_lt_edgeSlope x y hx hσ hij hjn hit htj hlt))
      hchord.symm
  · exact hle

/-- Monotone edge slopes force every ordered triple below the vertex bound to have nonnegative
oriented area. -/
theorem areasNonnegativeUpTo_of_slopesMonotoneUpTo (x y : ℕ → K) {n : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n) :
    AreasNonnegativeUpTo x y n := by
  intro i j k hij hjk hkn
  have hleft : chordSlope x y i j ≤ edgeSlope x y (j - 1) :=
    chordSlope_le_lastEdge x y hx hσ hij (hjk.trans hkn)
  have hmiddle : edgeSlope x y (j - 1) ≤ edgeSlope x y j :=
    hσ (by omega) (by omega)
  have hright : edgeSlope x y j ≤ chordSlope x y j k :=
    firstEdge_le_chordSlope x y hx hσ hjk hkn
  rw [orientedArea_eq_slopeDifference x y
    (ne_of_gt (hx hij (hjk.trans hkn))) (ne_of_gt (hx hjk hkn))]
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr (hx hij (hjk.trans hkn)).le)
      (sub_nonneg.mpr (hx hjk hkn).le))
    (sub_nonneg.mpr (hleft.trans (hmiddle.trans hright)))

/-- Nonnegative consecutive triangles imply monotonicity of every valid pair of edge slopes. -/
theorem slopesMonotoneUpTo_of_consecutiveAreasNonnegative (x y : ℕ → K) {n : ℕ}
    (hx : StrictlyIncreasingUpTo x n)
    (harea : ∀ i : ℕ, i + 2 < n → 0 ≤ orientedArea x y i (i + 1) (i + 2)) :
    SlopesMonotoneUpTo x y n := by
  intro i j hij hjn
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
      apply (ih (by omega)).trans
      rw [← orientedArea_consecutive_nonneg_iff x y
        (hx (by omega) (by omega)) (hx (by omega) (by omega))]
      exact harea j (by omega)

/-- For a chain with strictly increasing first coordinates, all ordered areas are nonnegative
exactly when the consecutive edge slopes are weakly increasing. -/
theorem areasNonnegativeUpTo_iff_slopesMonotoneUpTo (x y : ℕ → K) {n : ℕ}
    (hx : StrictlyIncreasingUpTo x n) :
    AreasNonnegativeUpTo x y n ↔ SlopesMonotoneUpTo x y n := by
  constructor
  · intro harea
    apply slopesMonotoneUpTo_of_consecutiveAreasNonnegative x y hx
    intro i hin
    exact harea (by omega) (by omega) hin
  · exact areasNonnegativeUpTo_of_slopesMonotoneUpTo x y hx

/-- Pairwise monotonicity of the valid edge slopes is equivalent to checking adjacent edges. -/
theorem slopesMonotoneUpTo_iff_consecutive (x y : ℕ → K) {n : ℕ}
    (hx : StrictlyIncreasingUpTo x n) :
    SlopesMonotoneUpTo x y n ↔
      ∀ i : ℕ, i + 2 < n → edgeSlope x y i ≤ edgeSlope x y (i + 1) := by
  constructor
  · intro hσ i hin
    exact hσ (Nat.le_succ i) hin
  · intro hσ
    apply slopesMonotoneUpTo_of_consecutiveAreasNonnegative x y hx
    intro i hin
    rw [orientedArea_consecutive_nonneg_iff x y
      (hx (by omega) (by omega)) (hx (by omega) (by omega))]
    exact hσ i hin

/-- It is enough to check the areas of consecutive triples in order to control every ordered
triple in a chain with strictly increasing first coordinates. -/
theorem areasNonnegativeUpTo_iff_consecutive (x y : ℕ → K) {n : ℕ}
    (hx : StrictlyIncreasingUpTo x n) :
    AreasNonnegativeUpTo x y n ↔
      ∀ i : ℕ, i + 2 < n → 0 ≤ orientedArea x y i (i + 1) (i + 2) := by
  constructor
  · intro harea i hin
    exact harea (by omega) (by omega) hin
  · intro harea
    exact areasNonnegativeUpTo_of_slopesMonotoneUpTo x y hx
      (slopesMonotoneUpTo_of_consecutiveAreasNonnegative x y hx harea)

/-- For a convex chain, a degenerate ordered triangle forces every edge between its first and
last vertices to have the same slope. -/
theorem slopesConstantBetween_of_orientedArea_eq_zero (x y : ℕ → K) {n i j k : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjk : j < k) (hkn : k < n)
    (harea : orientedArea x y i j k = 0) :
    SlopesConstantBetween x y i k := by
  have hxij : x i < x j := hx hij (hjk.trans hkn)
  have hxjk : x j < x k := hx hjk hkn
  have hproduct : (x j - x i) * (x k - x j) ≠ 0 :=
    ne_of_gt (mul_pos (sub_pos.mpr hxij) (sub_pos.mpr hxjk))
  have hslopeDiff : chordSlope x y j k - chordSlope x y i j = 0 := by
    rw [orientedArea_eq_slopeDifference x y (ne_of_gt hxij) (ne_of_gt hxjk)] at harea
    exact (mul_eq_zero.mp harea).resolve_left hproduct
  have hchord : chordSlope x y i j = chordSlope x y j k :=
    (sub_eq_zero.mp hslopeDiff).symm
  have hleft : chordSlope x y i j ≤ edgeSlope x y (j - 1) :=
    chordSlope_le_lastEdge x y hx hσ hij (hjk.trans hkn)
  have hmiddle : edgeSlope x y (j - 1) ≤ edgeSlope x y j :=
    hσ (by omega) (by omega)
  have hright : edgeSlope x y j ≤ chordSlope x y j k :=
    firstEdge_le_chordSlope x y hx hσ hjk hkn
  have hlast_le_left : edgeSlope x y (j - 1) ≤ chordSlope x y i j := by
    rw [hchord]
    exact hmiddle.trans hright
  have hright_le_first : chordSlope x y j k ≤ edgeSlope x y j := by
    rw [← hchord]
    exact hleft.trans hmiddle
  have hleftLast : chordSlope x y i j = edgeSlope x y (j - 1) :=
    le_antisymm hleft hlast_le_left
  have hrightFirst : chordSlope x y j k = edgeSlope x y j :=
    le_antisymm hright_le_first hright
  have hlastFirst : edgeSlope x y (j - 1) = edgeSlope x y j := by
    apply le_antisymm hmiddle
    calc
      edgeSlope x y j ≤ chordSlope x y j k := hright
      _ = chordSlope x y i j := hchord.symm
      _ ≤ edgeSlope x y (j - 1) := hleft
  have hiLast : edgeSlope x y i = edgeSlope x y (j - 1) :=
    edgeSlope_eq_lastEdge_of_chordSlope_eq x y hx hσ hij (hjk.trans hkn) le_rfl hij
      hleftLast
  intro t hit htk
  by_cases htj : t < j
  · have htLast : edgeSlope x y t = edgeSlope x y (j - 1) :=
      edgeSlope_eq_lastEdge_of_chordSlope_eq x y hx hσ hij (hjk.trans hkn) hit htj
        hleftLast
    exact htLast.trans hiLast.symm
  · have hjt : j ≤ t := Nat.le_of_not_gt htj
    have htFirst : edgeSlope x y t = edgeSlope x y j :=
      edgeSlope_eq_firstEdge_of_chordSlope_eq x y hx hσ hjk hkn hjt htk hrightFirst
    exact htFirst.trans (hlastFirst.symm.trans hiLast.symm)

/-- A constant run of edge slopes makes every triangle whose vertices lie in that run
degenerate. -/
theorem orientedArea_eq_zero_of_slopesConstantBetween (x y : ℕ → K) {n i j k : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hij : i < j) (hjk : j < k) (hkn : k < n)
    (hconstant : SlopesConstantBetween x y i k) :
    orientedArea x y i j k = 0 := by
  have hxij : x i < x j := hx hij (hjk.trans hkn)
  have hxjk : x j < x k := hx hjk hkn
  rw [orientedArea_eq_slopeDifference x y (ne_of_gt hxij) (ne_of_gt hxjk)]
  suffices chordSlope x y i j = edgeSlope x y i ∧
      chordSlope x y j k = edgeSlope x y i by
    rw [this.1, this.2, sub_self, mul_zero]
  constructor
  · rw [chordSlope]
    have hdx : x j - x i ≠ 0 := ne_of_gt (sub_pos.mpr hxij)
    apply (div_eq_iff hdx).2
    rw [← sum_horizontalIncrement_mul_edgeSlope x y hij.le]
    · rw [← sum_Ico_increment x hij.le]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have hit : i ≤ t := (Finset.mem_Ico.mp ht).1
      have htj : t < j := (Finset.mem_Ico.mp ht).2
      rw [hconstant hit (htj.trans hjk)]
      ring
    · intro t ht
      have htj : t < j := (Finset.mem_Ico.mp ht).2
      have ht1n : t + 1 < n :=
        lt_of_le_of_lt (Nat.succ_le_of_lt htj) (hjk.trans hkn)
      exact ne_of_lt (hx (Nat.lt_succ_self t) ht1n)
  · rw [chordSlope]
    have hdx : x k - x j ≠ 0 := ne_of_gt (sub_pos.mpr hxjk)
    apply (div_eq_iff hdx).2
    rw [← sum_horizontalIncrement_mul_edgeSlope x y hjk.le]
    · rw [← sum_Ico_increment x hjk.le]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      have htj : j ≤ t := (Finset.mem_Ico.mp ht).1
      have htk : t < k := (Finset.mem_Ico.mp ht).2
      rw [hconstant (hij.le.trans htj) htk]
      ring
    · intro t ht
      have htk : t < k := (Finset.mem_Ico.mp ht).2
      have ht1n : t + 1 < n := lt_of_le_of_lt (Nat.succ_le_of_lt htk) hkn
      exact ne_of_lt (hx (Nat.lt_succ_self t) ht1n)

/-- In a convex chain, an ordered triangle is degenerate exactly when all intervening edge slopes
are equal. -/
theorem orientedArea_eq_zero_iff_slopesConstantBetween (x y : ℕ → K) {n i j k : ℕ}
    (hx : StrictlyIncreasingUpTo x n) (hσ : SlopesMonotoneUpTo x y n)
    (hij : i < j) (hjk : j < k) (hkn : k < n) :
    orientedArea x y i j k = 0 ↔ SlopesConstantBetween x y i k := by
  constructor
  · exact slopesConstantBetween_of_orientedArea_eq_zero x y hx hσ hij hjk hkn
  · exact orientedArea_eq_zero_of_slopesConstantBetween x y hx hij hjk hkn

end DiscreteConvexChain

end ToeplitzPositroids
