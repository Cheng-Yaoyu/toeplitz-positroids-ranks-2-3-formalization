import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Monotone.Basic

/-!
# Finite skew shapes in a rectangle

The finite-factor Edrei argument only needs partitions inside a finite rectangle.  Encoding the
rectangle explicitly makes every cell set and every bounded filling definitionally finite.
-/

namespace ToeplitzPositroids.Edrei

/-- A partition with `r` rows whose row lengths are at most `w`. -/
structure RectanglePartition (r w : ℕ) where
  rowLength : Fin r → Fin (w + 1)
  antitone : Antitone rowLength

namespace RectanglePartition

instance {r w : ℕ} : CoeFun (RectanglePartition r w) (fun _ ↦ Fin r → ℕ) :=
  ⟨fun P i ↦ (P.rowLength i).val⟩

theorem rowLength_le_width {r w : ℕ} (P : RectanglePartition r w) (i : Fin r) :
    P i ≤ w := by
  exact Nat.le_of_lt_succ (P.rowLength i).isLt

theorem rowLength_injective {r w : ℕ} :
    Function.Injective (fun P : RectanglePartition r w ↦ P.rowLength) := by
  intro P Q h
  cases P
  cases Q
  congr

instance {r w : ℕ} : Finite (RectanglePartition r w) :=
  Finite.of_injective (fun P ↦ P.rowLength) rowLength_injective

noncomputable instance {r w : ℕ} : Fintype (RectanglePartition r w) :=
  Fintype.ofFinite _

end RectanglePartition

/-- A finite skew shape `outer / inner` in an `r × w` rectangle. -/
structure FiniteSkewShape (r w : ℕ) where
  inner : RectanglePartition r w
  outer : RectanglePartition r w
  inner_le_outer : ∀ i, inner i ≤ outer i

namespace FiniteSkewShape

theorem endpoints_injective {r w : ℕ} :
    Function.Injective (fun S : FiniteSkewShape r w ↦ (S.inner, S.outer)) := by
  intro S T h
  have hi : S.inner = T.inner := congrArg Prod.fst h
  have ho : S.outer = T.outer := congrArg Prod.snd h
  cases S
  cases T
  cases hi
  cases ho
  rfl

instance {r w : ℕ} : Finite (FiniteSkewShape r w) :=
  Finite.of_injective (fun S ↦ (S.inner, S.outer)) endpoints_injective

noncomputable instance {r w : ℕ} : Fintype (FiniteSkewShape r w) :=
  Fintype.ofFinite _

/-- Cells are indexed by zero-based row and column coordinates. -/
def cells {r w : ℕ} (S : FiniteSkewShape r w) : Finset (Fin r × Fin w) :=
  Finset.univ.filter fun x ↦ S.inner x.1 ≤ x.2.val ∧ x.2.val < S.outer x.1

@[simp]
theorem mem_cells {r w : ℕ} {S : FiniteSkewShape r w} {x : Fin r × Fin w} :
    x ∈ S.cells ↔ S.inner x.1 ≤ x.2.val ∧ x.2.val < S.outer x.1 := by
  simp [cells]

/-- The subtype of cells of a finite skew shape. -/
abbrev Cell {r w : ℕ} (S : FiniteSkewShape r w) :=
  {x : Fin r × Fin w // x ∈ S.cells}

/-- Cells in a fixed row. -/
def rowCells {r w : ℕ} (S : FiniteSkewShape r w) (i : Fin r) : Finset (Fin w) :=
  Finset.univ.filter fun j ↦ (i, j) ∈ S.cells

/-- Cells in a fixed column. -/
def columnCells {r w : ℕ} (S : FiniteSkewShape r w) (j : Fin w) : Finset (Fin r) :=
  Finset.univ.filter fun i ↦ (i, j) ∈ S.cells

@[simp]
theorem mem_rowCells {r w : ℕ} {S : FiniteSkewShape r w}
    {i : Fin r} {j : Fin w} :
    j ∈ S.rowCells i ↔ S.inner i ≤ j.val ∧ j.val < S.outer i := by
  simp [rowCells]

@[simp]
theorem mem_columnCells {r w : ℕ} {S : FiniteSkewShape r w}
    {i : Fin r} {j : Fin w} :
    i ∈ S.columnCells j ↔ S.inner i ≤ j.val ∧ j.val < S.outer i := by
  simp [columnCells]

/-- Number of cells in a fixed row. -/
def rowWidth {r w : ℕ} (S : FiniteSkewShape r w) (i : Fin r) : ℕ :=
  (S.rowCells i).card

/-- Number of cells in a fixed column. -/
def columnHeight {r w : ℕ} (S : FiniteSkewShape r w) (j : Fin w) : ℕ :=
  (S.columnCells j).card

/-- Row width is the difference of the outer and inner row lengths. -/
theorem rowWidth_eq_sub {r w : ℕ} (S : FiniteSkewShape r w) (i : Fin r) :
    S.rowWidth i = S.outer i - S.inner i := by
  have hmap : (S.rowCells i).map Fin.valEmbedding =
      Finset.Ico (S.inner i) (S.outer i) := by
    ext j
    constructor
    · intro hj
      obtain ⟨a, ha, haj⟩ := Finset.mem_map.mp hj
      have ha' := (mem_rowCells.mp ha)
      subst j
      exact Finset.mem_Ico.mpr ha'
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      have hjw : j < w := hj'.2.trans_le (S.outer.rowLength_le_width i)
      apply Finset.mem_map.mpr
      exact ⟨⟨j, hjw⟩, mem_rowCells.mpr hj', rfl⟩
  have hcard := congrArg Finset.card hmap
  rw [Finset.card_map, Nat.card_Ico] at hcard
  exact hcard

/-- Every column has at most `p` cells. -/
def FitsColumnBound {r w : ℕ} (S : FiniteSkewShape r w) (p : ℕ) : Prop :=
  ∀ j, S.columnHeight j ≤ p

/-- Every row has at most `q` cells. -/
def FitsRowBound {r w : ℕ} (S : FiniteSkewShape r w) (q : ℕ) : Prop :=
  ∀ i, S.rowWidth i ≤ q

theorem fitsRowBound_iff {r w : ℕ} (S : FiniteSkewShape r w) (q : ℕ) :
    S.FitsRowBound q ↔ ∀ i, S.outer i - S.inner i ≤ q := by
  simp [FitsRowBound, rowWidth_eq_sub]

noncomputable instance {r w : ℕ} (S : FiniteSkewShape r w) (p : ℕ) :
    Decidable (S.FitsColumnBound p) := Classical.dec _

noncomputable instance {r w : ℕ} (S : FiniteSkewShape r w) (q : ℕ) :
    Decidable (S.FitsRowBound q) := Classical.dec _

end FiniteSkewShape

end ToeplitzPositroids.Edrei
