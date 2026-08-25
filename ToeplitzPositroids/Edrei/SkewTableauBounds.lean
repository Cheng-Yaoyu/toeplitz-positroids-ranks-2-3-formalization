import ToeplitzPositroids.Edrei.SkewTableauShape
import Mathlib.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-!
# Finite strip bounds for skew shapes

This file supplies the finite combinatorial lemma needed to pass between the zero-tail partition
form of the Edrei hook condition and the bounded skew-tableau form.  A column of a skew shape is
an interval of rows: the antitone inner and outer partitions therefore turn a bound on every
`p`-shifted pair of rows into a bound of `p` on every column.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

theorem FiniteSkewShape.fitsColumnBound_iff_shift
    {r w p : ℕ} (S : FiniteSkewShape r w) :
    S.FitsColumnBound p ↔
      ∀ t : Fin (r - p),
        S.outer ⟨t.val + p, by omega⟩ ≤ S.inner ⟨t.val, by omega⟩ := by
  constructor
  · intro hfit t
    by_contra hbad
    have houter : S.inner ⟨t.val, by omega⟩ <
        S.outer ⟨t.val + p, by omega⟩ := by omega
    let c : Fin w := ⟨S.inner ⟨t.val, by omega⟩, by
      have hwidth := S.outer.rowLength_le_width ⟨t.val + p, by omega⟩
      omega⟩
    let A := {k : Fin (p + 1) // True}
    let f : A → {i : Fin r // i ∈ S.columnCells c} := fun k ↦
      ⟨⟨t.val + k.val, by omega⟩, by
        rw [FiniteSkewShape.mem_columnCells]
        constructor
        · have hinner := S.inner.antitone (show
            (⟨t.val, by omega⟩ : Fin r) ≤ ⟨t.val + k.val, by omega⟩ by
              change t.val ≤ t.val + k.val
              omega)
          change S.inner ⟨t.val + k.val, by omega⟩ ≤ c.val
          simpa [c] using hinner
        · have houtermono := S.outer.antitone (show
            (⟨t.val + k.val, by omega⟩ : Fin r) ≤ ⟨t.val + p, by omega⟩ by
              change t.val + k.val ≤ t.val + p
              omega)
          change c.val < S.outer ⟨t.val + k.val, by omega⟩
          exact houter.trans_le houtermono⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      have hval := congrArg (fun z : {i : Fin r // i ∈ S.columnCells c} ↦ z.val.val) hxy
      dsimp [f] at hval
      omega
    have hcard := Fintype.card_le_of_injective f hf
    have hcard' : p + 1 ≤ (S.columnCells c).card := by
      have hAcard : Fintype.card A = p + 1 := by
        dsimp [A]
        simp
      have hcolcard : Fintype.card {i : Fin r // i ∈ S.columnCells c} =
          (S.columnCells c).card := by
        rw [Fintype.card_subtype]
        simp [FiniteSkewShape.columnCells]
      have hcardA : p + 1 ≤ Fintype.card {i : Fin r // i ∈ S.columnCells c} := by
        rw [← hAcard]
        exact hcard
      simpa only [hcolcard] using hcardA
    have hfitc := hfit c
    change (S.columnCells c).card ≤ p at hfitc
    omega
  · intro hshift c
    by_cases hempty : (S.columnCells c).Nonempty
    · let m := (S.columnCells c).min' hempty
      let A := {i : Fin r // i ∈ S.columnCells c}
      let f : A → Fin p := fun i ↦ ⟨i.val.val - m, by
        have hmi : m ≤ i.val.val := Finset.min'_le _ _ i.property
        by_contra hnot
        have hp : p ≤ i.val.val - m := by omega
        have hmp : m + p ≤ i.val.val := by omega
        have hmBound : m + p < r := by omega
        have hhook := hshift ⟨m, by omega⟩
        have hhook' : S.outer ⟨m + p, hmBound⟩ ≤ S.inner m := by
          simpa using hhook
        have hmcell := FiniteSkewShape.mem_columnCells.mp
          (Finset.min'_mem (S.columnCells c) hempty)
        have hinner : S.inner m ≤ c.val := hmcell.1
        have houter : c.val < S.outer i.val :=
          (FiniteSkewShape.mem_columnCells.mp i.property).2
        have houtermono : S.outer i.val ≤ S.outer ⟨m + p, hmBound⟩ :=
          S.outer.antitone hmp
        omega⟩
      have hf : Function.Injective f := by
        intro i j hij
        apply Subtype.ext
        apply Fin.ext
        have hmi : m ≤ i.val.val := Finset.min'_le _ _ i.property
        have hmj : m ≤ j.val.val := Finset.min'_le _ _ j.property
        have hval := congrArg Fin.val hij
        dsimp [f] at hval
        omega
      have hcard := Fintype.card_le_of_injective f hf
      have hcard' : (S.columnCells c).card ≤ p := by
        have hAcard : Fintype.card A = (S.columnCells c).card := by
          rw [Fintype.card_subtype]
          simp [FiniteSkewShape.columnCells]
        simpa [hAcard, FiniteSkewShape.columnHeight] using hcard
      exact hcard'
    · simp [Finset.not_nonempty_iff_eq_empty.mp hempty,
        FiniteSkewShape.columnHeight]

end ToeplitzPositroids.Edrei
