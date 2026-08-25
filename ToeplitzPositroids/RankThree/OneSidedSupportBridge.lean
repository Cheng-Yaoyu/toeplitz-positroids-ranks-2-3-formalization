import ToeplitzPositroids.RankThree.OneSidedExactSupport
import Mathlib.Tactic

/-!
# Exact support bridge for one-sided realizations

This file normalizes the compatible-data triple rule to increasing ordered triples.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- The finite set underlying an increasingly selected triple. -/
def selectedTripleFinset {n : ℕ} (cols : Fin 3 ↪o Fin n) : Finset (Fin n) :=
  Finset.univ.image cols

theorem selectedTripleFinset_eq {n : ℕ} (cols : Fin 3 ↪o Fin n) :
    selectedTripleFinset cols = {cols 0, cols 1, cols 2} := by
  ext x
  simp only [selectedTripleFinset, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · intro hx
    rcases hx with hx | hx | hx
    · exact ⟨0, hx.symm⟩
    · exact ⟨1, hx.symm⟩
    · exact ⟨2, hx.symm⟩

@[simp]
theorem selectedTripleFinset_card {n : ℕ} (cols : Fin 3 ↪o Fin n) :
    (selectedTripleFinset cols).card = 3 := by
  rw [selectedTripleFinset_eq]
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  simp [h01, h02, h12]

/-- The loop part of the compatible triple rule on an ordered triple. -/
theorem meetsLoops_selectedTriple_iff {n : ℕ} (D : CompatibleRankThreeData n)
    (cols : Fin 3 ↪o Fin n) :
    D.MeetsLoops (selectedTripleFinset cols) ↔
      D.IsLoop (cols 0) ∨ D.IsLoop (cols 1) ∨ D.IsLoop (cols 2) := by
  rw [selectedTripleFinset_eq]
  simp [CompatibleRankThreeData.MeetsLoops]

private theorem two_le_card_filter_three {E : Type*} [DecidableEq E]
    (P : E → Prop) [DecidablePred P] {a b c : E}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    2 ≤ (Finset.filter P {a, b, c}).card ↔
      (P a ∧ P b) ∨ (P a ∧ P c) ∨ (P b ∧ P c) := by
  by_cases ha : P a <;> by_cases hb : P b <;> by_cases hc : P c <;>
    simp [Finset.filter_insert, Finset.filter_singleton, ha, hb, hc, hab, hac, hbc]

theorem containsInitialParallelPair_selectedTriple_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (cols : Fin 3 ↪o Fin n) :
    D.ContainsInitialParallelPair (selectedTripleFinset cols) ↔
      (D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 1)) ∨
      (D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 2)) ∨
      (D.IsInitialParallel (cols 1) ∧ D.IsInitialParallel (cols 2)) := by
  rw [selectedTripleFinset_eq]
  unfold CompatibleRankThreeData.ContainsInitialParallelPair
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  exact two_le_card_filter_three D.IsInitialParallel h01 h02 h12

theorem containsTerminalParallelPair_selectedTriple_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (cols : Fin 3 ↪o Fin n) :
    D.ContainsTerminalParallelPair (selectedTripleFinset cols) ↔
      (D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 1)) ∨
      (D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 2)) ∨
      (D.IsTerminalParallel (cols 1) ∧ D.IsTerminalParallel (cols 2)) := by
  rw [selectedTripleFinset_eq]
  unfold CompatibleRankThreeData.ContainsTerminalParallelPair
  have h01 : cols 0 ≠ cols 1 := ne_of_lt (cols.strictMono (by decide))
  have h02 : cols 0 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  have h12 : cols 1 ≠ cols 2 := ne_of_lt (cols.strictMono (by decide))
  exact two_le_card_filter_three D.IsTerminalParallel h01 h02 h12

/-- The compatible triple rule in ordered-column form. -/
theorem tripleNonbasis_selectedTriple_iff {n : ℕ} (D : CompatibleRankThreeData n)
    (cols : Fin 3 ↪o Fin n) :
    D.TripleNonbasis (selectedTripleFinset cols) ↔
      (D.IsLoop (cols 0) ∨ D.IsLoop (cols 1) ∨ D.IsLoop (cols 2)) ∨
      ((D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 1)) ∨
        (D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 2)) ∨
        (D.IsInitialParallel (cols 1) ∧ D.IsInitialParallel (cols 2))) ∨
      ((D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 1)) ∨
        (D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 2)) ∨
        (D.IsTerminalParallel (cols 1) ∧ D.IsTerminalParallel (cols 2))) ∨
      ((D.simplifiedImages (selectedTripleFinset cols)).card = 3 ∧
        D.SimplifiedCollinear (D.simplifiedImages (selectedTripleFinset cols))) := by
  unfold CompatibleRankThreeData.TripleNonbasis
  rw [selectedTripleFinset_card]
  simp only [true_and]
  rw [meetsLoops_selectedTriple_iff, containsInitialParallelPair_selectedTriple_iff,
    containsTerminalParallelPair_selectedTriple_iff]

/-- The simplified images of a nonloop ordered triple are its three explicit class indices. -/
theorem simplifiedImages_selectedTriple_eq {n : ℕ} (D : CompatibleRankThreeData n)
    (cols : Fin 3 ↪o Fin n) (h0 : D.IsNonloop (cols 0))
    (h1 : D.IsNonloop (cols 1)) (h2 : D.IsNonloop (cols 2)) :
    D.simplifiedImages (selectedTripleFinset cols) =
      {D.simplifiedIndex (cols 0), D.simplifiedIndex (cols 1), D.simplifiedIndex (cols 2)} := by
  rw [selectedTripleFinset_eq]
  ext x
  simp [CompatibleRankThreeData.simplifiedImages,
    CompatibleRankThreeData.simplifiedIndex?, h0, h1, h2]
  tauto

private theorem card_insert_three_eq_three_iff {E : Type*} [DecidableEq E] (a b c : E) :
    ({a, b, c} : Finset E).card = 3 ↔ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;>
    simp [hab, hac, hbc]

/-- The three-distinct-image collinearity clause in explicit ordered form. -/
theorem distinctImages_collinear_selectedTriple_iff {n : ℕ}
    (D : CompatibleRankThreeData n) (cols : Fin 3 ↪o Fin n)
    (h0 : D.IsNonloop (cols 0)) (h1 : D.IsNonloop (cols 1))
    (h2 : D.IsNonloop (cols 2)) :
    ((D.simplifiedImages (selectedTripleFinset cols)).card = 3 ∧
        D.SimplifiedCollinear (D.simplifiedImages (selectedTripleFinset cols))) ↔
      D.simplifiedIndex (cols 0) ≠ D.simplifiedIndex (cols 1) ∧
      D.simplifiedIndex (cols 0) ≠ D.simplifiedIndex (cols 2) ∧
      D.simplifiedIndex (cols 1) ≠ D.simplifiedIndex (cols 2) ∧
      ∃ H ∈ D.intervals,
        D.simplifiedIndex (cols 0) ∈ H.points ∧
        D.simplifiedIndex (cols 1) ∈ H.points ∧
        D.simplifiedIndex (cols 2) ∈ H.points := by
  rw [simplifiedImages_selectedTriple_eq D cols h0 h1 h2,
    card_insert_three_eq_three_iff]
  unfold CompatibleRankThreeData.SimplifiedCollinear
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
  tauto

/-- Explicit ordered form of the compatible nonbasis rule. -/
def OrderedCompatibleNonbasis {n : ℕ} (D : CompatibleRankThreeData n)
    (cols : Fin 3 ↪o Fin n) : Prop :=
  D.IsLoop (cols 0) ∨ D.IsLoop (cols 1) ∨ D.IsLoop (cols 2) ∨
  ((D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 1)) ∨
    (D.IsInitialParallel (cols 0) ∧ D.IsInitialParallel (cols 2)) ∨
    (D.IsInitialParallel (cols 1) ∧ D.IsInitialParallel (cols 2))) ∨
  ((D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 1)) ∨
    (D.IsTerminalParallel (cols 0) ∧ D.IsTerminalParallel (cols 2)) ∨
    (D.IsTerminalParallel (cols 1) ∧ D.IsTerminalParallel (cols 2))) ∨
  (D.simplifiedIndex (cols 0) ≠ D.simplifiedIndex (cols 1) ∧
    D.simplifiedIndex (cols 0) ≠ D.simplifiedIndex (cols 2) ∧
    D.simplifiedIndex (cols 1) ≠ D.simplifiedIndex (cols 2) ∧
    ∃ H ∈ D.intervals,
      D.simplifiedIndex (cols 0) ∈ H.points ∧
      D.simplifiedIndex (cols 1) ∈ H.points ∧
      D.simplifiedIndex (cols 2) ∈ H.points)

/-- The ordered condition is exactly `CompatibleRankThreeData.TripleNonbasis`. -/
theorem tripleNonbasis_selectedTriple_iff_ordered {n : ℕ}
    (D : CompatibleRankThreeData n) (cols : Fin 3 ↪o Fin n) :
    D.TripleNonbasis (selectedTripleFinset cols) ↔ OrderedCompatibleNonbasis D cols := by
  rw [tripleNonbasis_selectedTriple_iff]
  by_cases h0 : D.IsLoop (cols 0)
  · simp [OrderedCompatibleNonbasis, h0]
  by_cases h1 : D.IsLoop (cols 1)
  · simp [OrderedCompatibleNonbasis, h1]
  by_cases h2 : D.IsLoop (cols 2)
  · simp [OrderedCompatibleNonbasis, h2]
  have hn0 : D.IsNonloop (cols 0) := (D.isNonloop_iff_not_isLoop _).2 h0
  have hn1 : D.IsNonloop (cols 1) := (D.isNonloop_iff_not_isLoop _).2 h1
  have hn2 : D.IsNonloop (cols 2) := (D.isNonloop_iff_not_isLoop _).2 h2
  rw [distinctImages_collinear_selectedTriple_iff D cols hn0 hn1 hn2]
  simp [OrderedCompatibleNonbasis, h0, h1, h2]

end

end ToeplitzPositroids.RankThree
