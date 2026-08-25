import ToeplitzPositroids.Edrei.SkewTableauShape
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Real.Basic

/-!
# Bounded semistandard skew tableaux

Two tableau orientations occur in the supersymmetric expansion.  Alpha tableaux are weak along
rows and strict down columns; beta tableaux are the transposed convention.  Since both the shape
and alphabet are finite, the resulting types carry canonical finite enumerations.
-/

namespace ToeplitzPositroids.Edrei

/-- Rank of `x` among the elements of `s`, counting elements strictly below it. -/
def finsetRank {m : ℕ} (s : Finset (Fin m)) (x : Fin m) : ℕ :=
  (s.filter fun y ↦ y < x).card

theorem finsetRank_lt_card {m : ℕ} {s : Finset (Fin m)} {x : Fin m} (hx : x ∈ s) :
    finsetRank s x < s.card := by
  apply Finset.card_lt_card
  exact Finset.filter_ssubset.mpr ⟨x, hx, lt_irrefl x⟩

/-- An alpha-oriented semistandard filling of a finite skew shape. -/
structure AlphaSkewTableau {r w : ℕ} (S : FiniteSkewShape r w) (p : ℕ) where
  entry : S.Cell → Fin p
  row_weak : ∀ {x y : S.Cell}, x.val.1 = y.val.1 →
    x.val.2 ≤ y.val.2 → entry x ≤ entry y
  column_strict : ∀ {x y : S.Cell}, x.val.2 = y.val.2 →
    x.val.1 < y.val.1 → entry x < entry y

/-- A beta-oriented semistandard filling, equivalently an ordinary tableau of transposed shape. -/
structure BetaSkewTableau {r w : ℕ} (S : FiniteSkewShape r w) (q : ℕ) where
  entry : S.Cell → Fin q
  row_strict : ∀ {x y : S.Cell}, x.val.1 = y.val.1 →
    x.val.2 < y.val.2 → entry x < entry y
  column_weak : ∀ {x y : S.Cell}, x.val.2 = y.val.2 →
    x.val.1 ≤ y.val.1 → entry x ≤ entry y

namespace AlphaSkewTableau

/-- The canonical alpha filling labels a cell by its rank down its column. -/
def ofFitsColumnBound {r w p : ℕ} {S : FiniteSkewShape r w}
    (hfit : S.FitsColumnBound p) : AlphaSkewTableau S p where
  entry x := ⟨finsetRank (S.columnCells x.val.2) x.val.1, by
    exact (finsetRank_lt_card ((FiniteSkewShape.mem_columnCells).2
      (FiniteSkewShape.mem_cells.mp x.property))).trans_le (hfit x.val.2)⟩
  row_weak := by
    intro x y hrow hcol
    change finsetRank (S.columnCells x.val.2) x.val.1 ≤
      finsetRank (S.columnCells y.val.2) y.val.1
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter] at hi ⊢
    refine ⟨?_, by simpa [hrow] using hi.2⟩
    rw [FiniteSkewShape.mem_columnCells] at hi ⊢
    have hxyRow : x.val.1 = y.val.1 := hrow
    have hirow : i < y.val.1 := by simpa [← hxyRow] using hi.2
    have houter := S.outer.antitone (le_of_lt hirow)
    have hyCell := FiniteSkewShape.mem_cells.mp y.property
    exact ⟨hi.1.1.trans hcol, hyCell.2.trans_le houter⟩
  column_strict := by
    intro x y hcol hrow
    change finsetRank (S.columnCells x.val.2) x.val.1 <
      finsetRank (S.columnCells y.val.2) y.val.1
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨by simpa [hcol] using hi.1, hi.2.trans hrow⟩
    · intro heq
      have hxmem : x.val.1 ∈
          (S.columnCells y.val.2).filter fun i ↦ i < y.val.1 := by
        simp only [Finset.mem_filter]
        exact ⟨by
          apply FiniteSkewShape.mem_columnCells.mpr
          simpa [hcol] using FiniteSkewShape.mem_cells.mp x.property, hrow⟩
      rw [← heq] at hxmem
      exact (Finset.mem_filter.mp hxmem).2.false

theorem entry_injective {r w p : ℕ} {S : FiniteSkewShape r w} :
    Function.Injective (fun T : AlphaSkewTableau S p ↦ T.entry) := by
  intro T U h
  cases T
  cases U
  congr

instance {r w p : ℕ} {S : FiniteSkewShape r w} :
    Finite (AlphaSkewTableau S p) :=
  Finite.of_injective (fun T ↦ T.entry) entry_injective

noncomputable instance {r w p : ℕ} {S : FiniteSkewShape r w} :
    Fintype (AlphaSkewTableau S p) := Fintype.ofFinite _

/-- The alpha monomial attached to a tableau. -/
def weight {r w p : ℕ} {S : FiniteSkewShape r w}
    (alpha : Fin p → ℝ) (T : AlphaSkewTableau S p) : ℝ :=
  ∏ x : S.Cell, alpha (T.entry x)

theorem weight_pos {r w p : ℕ} {S : FiniteSkewShape r w}
    {alpha : Fin p → ℝ} (halpha : ∀ i, 0 < alpha i)
    (T : AlphaSkewTableau S p) :
    0 < weight alpha T := by
  unfold weight
  exact Finset.prod_pos fun x _ ↦ halpha (T.entry x)

/-- Existence of an alpha tableau forces the column-height bound. -/
theorem fitsColumnBound {r w p : ℕ} {S : FiniteSkewShape r w}
    (T : AlphaSkewTableau S p) : S.FitsColumnBound p := by
  intro j
  let A := {i : Fin r // i ∈ S.columnCells j}
  let f : A → Fin p := fun i ↦ T.entry ⟨(i.val, j), by
    simpa [FiniteSkewShape.columnCells] using i.property⟩
  have hf : Function.Injective f := by
    intro i k hik
    have hiCell : (i.val, j) ∈ S.cells := by
      simpa [FiniteSkewShape.columnCells] using i.property
    have hkCell : (k.val, j) ∈ S.cells := by
      simpa [FiniteSkewShape.columnCells] using k.property
    have hentry : T.entry ⟨(i.val, j), hiCell⟩ = T.entry ⟨(k.val, j), hkCell⟩ := by
      exact hik
    apply Subtype.ext
    rcases lt_trichotomy i.val k.val with hik' | hik' | hik'
    · have hlt := T.column_strict (x := ⟨(i.val, j), hiCell⟩)
          (y := ⟨(k.val, j), hkCell⟩) rfl hik'
      exact False.elim ((ne_of_lt hlt) hentry)
    · exact hik'
    · have hlt := T.column_strict (x := ⟨(k.val, j), hkCell⟩)
          (y := ⟨(i.val, j), hiCell⟩) rfl hik'
      exact False.elim ((ne_of_lt hlt) hentry.symm)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  have hAcard : Fintype.card A = (S.columnCells j).card := by
    dsimp only [A]
    rw [Fintype.card_subtype]
    simp [FiniteSkewShape.columnCells]
  rw [FiniteSkewShape.columnHeight, ← hAcard]
  exact hcard

theorem nonempty_iff_fitsColumnBound {r w p : ℕ} {S : FiniteSkewShape r w} :
    Nonempty (AlphaSkewTableau S p) ↔ S.FitsColumnBound p :=
  ⟨fun ⟨T⟩ ↦ T.fitsColumnBound, fun h ↦ ⟨ofFitsColumnBound h⟩⟩

end AlphaSkewTableau

namespace BetaSkewTableau

/-- The canonical beta filling labels a cell by its rank along its row. -/
def ofFitsRowBound {r w q : ℕ} {S : FiniteSkewShape r w}
    (hfit : S.FitsRowBound q) : BetaSkewTableau S q where
  entry x := ⟨finsetRank (S.rowCells x.val.1) x.val.2, by
    exact (finsetRank_lt_card ((FiniteSkewShape.mem_rowCells).2
      (FiniteSkewShape.mem_cells.mp x.property))).trans_le (hfit x.val.1)⟩
  row_strict := by
    intro x y hrow hcol
    change finsetRank (S.rowCells x.val.1) x.val.2 <
      finsetRank (S.rowCells y.val.1) y.val.2
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro j hj
      simp only [Finset.mem_filter] at hj ⊢
      exact ⟨by simpa [hrow] using hj.1, hj.2.trans hcol⟩
    · intro heq
      have hxmem : x.val.2 ∈ (S.rowCells y.val.1).filter fun j ↦ j < y.val.2 := by
        simp only [Finset.mem_filter]
        exact ⟨by
          apply FiniteSkewShape.mem_rowCells.mpr
          simpa [hrow] using FiniteSkewShape.mem_cells.mp x.property, hcol⟩
      rw [← heq] at hxmem
      exact (Finset.mem_filter.mp hxmem).2.false
  column_weak := by
    intro x y hcol hrow
    change finsetRank (S.rowCells x.val.1) x.val.2 ≤
      finsetRank (S.rowCells y.val.1) y.val.2
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter] at hj ⊢
    refine ⟨?_, by simpa [hcol] using hj.2⟩
    rw [FiniteSkewShape.mem_rowCells] at hj ⊢
    have hinner := S.inner.antitone hrow
    change S.inner y.val.1 ≤ S.inner x.val.1 at hinner
    have hyCell := FiniteSkewShape.mem_cells.mp y.property
    have hjlt : j.val < y.val.2.val := by simpa [hcol] using hj.2
    exact ⟨hinner.trans hj.1.1, hjlt.trans hyCell.2⟩

theorem entry_injective {r w q : ℕ} {S : FiniteSkewShape r w} :
    Function.Injective (fun T : BetaSkewTableau S q ↦ T.entry) := by
  intro T U h
  cases T
  cases U
  congr

instance {r w q : ℕ} {S : FiniteSkewShape r w} :
    Finite (BetaSkewTableau S q) :=
  Finite.of_injective (fun T ↦ T.entry) entry_injective

noncomputable instance {r w q : ℕ} {S : FiniteSkewShape r w} :
    Fintype (BetaSkewTableau S q) := Fintype.ofFinite _

/-- The beta monomial attached to a tableau. -/
def weight {r w q : ℕ} {S : FiniteSkewShape r w}
    (beta : Fin q → ℝ) (T : BetaSkewTableau S q) : ℝ :=
  ∏ x : S.Cell, beta (T.entry x)

theorem weight_pos {r w q : ℕ} {S : FiniteSkewShape r w}
    {beta : Fin q → ℝ} (hbeta : ∀ i, 0 < beta i)
    (T : BetaSkewTableau S q) :
    0 < weight beta T := by
  unfold weight
  exact Finset.prod_pos fun x _ ↦ hbeta (T.entry x)

/-- Existence of a beta tableau forces the row-width bound. -/
theorem fitsRowBound {r w q : ℕ} {S : FiniteSkewShape r w}
    (T : BetaSkewTableau S q) : S.FitsRowBound q := by
  intro i
  let A := {j : Fin w // j ∈ S.rowCells i}
  let f : A → Fin q := fun j ↦ T.entry ⟨(i, j.val), by
    simpa [FiniteSkewShape.rowCells] using j.property⟩
  have hf : Function.Injective f := by
    intro j k hjk
    have hjCell : (i, j.val) ∈ S.cells := by
      simpa [FiniteSkewShape.rowCells] using j.property
    have hkCell : (i, k.val) ∈ S.cells := by
      simpa [FiniteSkewShape.rowCells] using k.property
    have hentry : T.entry ⟨(i, j.val), hjCell⟩ = T.entry ⟨(i, k.val), hkCell⟩ := hjk
    apply Subtype.ext
    rcases lt_trichotomy j.val k.val with hjk' | hjk' | hjk'
    · have hlt := T.row_strict (x := ⟨(i, j.val), hjCell⟩)
          (y := ⟨(i, k.val), hkCell⟩) rfl hjk'
      exact False.elim ((ne_of_lt hlt) hentry)
    · exact hjk'
    · have hlt := T.row_strict (x := ⟨(i, k.val), hkCell⟩)
          (y := ⟨(i, j.val), hjCell⟩) rfl hjk'
      exact False.elim ((ne_of_lt hlt) hentry.symm)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  have hAcard : Fintype.card A = (S.rowCells i).card := by
    dsimp only [A]
    rw [Fintype.card_subtype]
    simp [FiniteSkewShape.rowCells]
  rw [FiniteSkewShape.rowWidth, ← hAcard]
  exact hcard

theorem nonempty_iff_fitsRowBound {r w q : ℕ} {S : FiniteSkewShape r w} :
    Nonempty (BetaSkewTableau S q) ↔ S.FitsRowBound q :=
  ⟨fun ⟨T⟩ ↦ T.fitsRowBound, fun h ↦ ⟨ofFitsRowBound h⟩⟩

end BetaSkewTableau

end ToeplitzPositroids.Edrei
