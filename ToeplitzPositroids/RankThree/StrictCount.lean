import ToeplitzPositroids.RankThree.ConvexMatrix
import ToeplitzPositroids.RankThree.SupportUniqueness
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Counting supports in the strict order-two region

This file formalizes the combinatorial and injectivity parts of Corollary 9. A slope-equality
pattern is a subset of the `n - 2` adjacent edge comparisons. Consecutive maximal minors recover
that subset exactly, while convexity shows that it determines every maximal-minor zero.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

variable {n : ℕ}

/-- A positive three-row matrix whose two-by-two ordered minors are all positive. -/
def InStrictOrderTwoRegion (A : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 < A i j) ∧
    ∀ (rows : Fin 2 ↪o Fin 3) (cols : Fin 2 ↪o Fin n),
      0 < orderedMinor A rows cols

/-- The coefficient-centered strict region for a three-row finite Toeplitz matrix. -/
def InStrictToeplitzRegion (a : Fin (n + 2) → ℝ) : Prop :=
  InStrictOrderTwoRegion (rankThreeToeplitz a)

/-- Strict order-two positivity implies total nonnegativity through order two. -/
theorem InStrictOrderTwoRegion.tnUpTo_two {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : InStrictOrderTwoRegion A) :
    TNUpTo A 2 := by
  intro k hk rows cols
  interval_cases k
  · simp
  · simpa using (hA.1 (rows 0) (cols 0)).le
  · exact (hA.2 rows cols).le

/-- Strict order-two positivity excludes loops and positive parallel pairs. -/
theorem InStrictOrderTwoRegion.isSimpleNonloopConfiguration
    {A : Matrix (Fin 3) (Fin n) ℝ} (hA : InStrictOrderTwoRegion A) :
    IsSimpleNonloopConfiguration A := by
  constructor
  · intro j hj
    rw [IsLoop] at hj
    have hzero := congrFun hj (0 : Fin 3)
    change A 0 j = 0 at hzero
    have hpos := hA.1 0 j
    linarith
  · intro i j hij hpar
    let rows : Fin 2 ↪o Fin 3 := Fin.castLEOrderEmb (by omega)
    let cols : Fin 2 ↪o Fin n := selectedPairEmbedding i j hij
    have hpos := hA.2 rows cols
    rcases hpar with ⟨c, _, hcol⟩
    have hcol0 := congrFun hcol (rows 0)
    have hcol1 := congrFun hcol (rows 1)
    have hzero : orderedMinor A rows cols = 0 := by
      rw [orderedMinor_two]
      simp only [cols, selectedPairEmbedding_zero, selectedPairEmbedding_one]
      change A (rows 0) i * A (rows 1) j - A (rows 0) j * A (rows 1) i = 0
      change A (rows 0) j = c * A (rows 0) i at hcol0
      change A (rows 1) j = c * A (rows 1) i at hcol1
      rw [hcol0, hcol1]
      ring
    linarith

/-- The three consecutive columns beginning at comparison index `i`. -/
def strictConsecutiveTripleEmbedding (i : Fin (n - 2)) : Fin 3 ↪o Fin n :=
  OrderEmbedding.ofStrictMono
    (fun j : Fin 3 ↦ ⟨i.val + j.val, by omega⟩)
    (by
      intro a b hab
      simp only [Fin.mk_lt_mk]
      omega)

@[simp]
theorem strictConsecutiveTripleEmbedding_apply (i : Fin (n - 2)) (j : Fin 3) :
    (strictConsecutiveTripleEmbedding i j).val = i.val + j.val :=
  rfl

/-- The subset of adjacent comparisons at which consecutive moment slopes are equal. -/
def slopeEqualityPattern (A : Matrix (Fin 3) (Fin n) ℝ) : Finset (Fin (n - 2)) :=
  Finset.univ.filter fun i ↦
    edgeSlope (matrixMomentU A) (matrixMomentV A) i.val =
      edgeSlope (matrixMomentU A) (matrixMomentV A) (i.val + 1)

@[simp]
theorem mem_slopeEqualityPattern_iff (A : Matrix (Fin 3) (Fin n) ℝ)
    (i : Fin (n - 2)) :
    i ∈ slopeEqualityPattern A ↔
      edgeSlope (matrixMomentU A) (matrixMomentV A) i.val =
        edgeSlope (matrixMomentU A) (matrixMomentV A) (i.val + 1) := by
  simp [slopeEqualityPattern]

/-- The consecutive maximal-minor zero pattern. -/
def consecutiveMinorZeroPattern (A : Matrix (Fin 3) (Fin n) ℝ) :
    Finset (Fin (n - 2)) :=
  Finset.univ.filter fun i ↦
    orderedMinor A (allRows 3) (strictConsecutiveTripleEmbedding i) = 0

@[simp]
theorem mem_consecutiveMinorZeroPattern_iff (A : Matrix (Fin 3) (Fin n) ℝ)
    (i : Fin (n - 2)) :
    i ∈ consecutiveMinorZeroPattern A ↔
      orderedMinor A (allRows 3) (strictConsecutiveTripleEmbedding i) = 0 := by
  simp [consecutiveMinorZeroPattern]

/-- In the simple `TN₂` region, a consecutive maximal minor vanishes exactly at an adjacent
slope equality. -/
theorem consecutiveMinor_eq_zero_iff_adjacentSlope_eq
    {A : Matrix (Fin 3) (Fin n) ℝ} (hTN2 : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) (i : Fin (n - 2)) :
    orderedMinor A (allRows 3) (strictConsecutiveTripleEmbedding i) = 0 ↔
      edgeSlope (matrixMomentU A) (matrixMomentV A) i.val =
        edgeSlope (matrixMomentU A) (matrixMomentV A) (i.val + 1) := by
  let i₀ : Fin n := ⟨i.val, by omega⟩
  let i₁ : Fin n := ⟨i.val + 1, by omega⟩
  let i₂ : Fin n := ⟨i.val + 2, by omega⟩
  have h₀₁ : i₀ < i₁ := by simp [i₀, i₁]
  have h₁₂ : i₁ < i₂ := by simp [i₁, i₂]
  have hembed :
      strictConsecutiveTripleEmbedding i = selectedTripleEmbedding i₀ i₁ i₂ h₀₁ h₁₂ := by
    apply RelEmbedding.ext
    intro j
    fin_cases j <;> rfl
  rw [hembed,
    orderedMinor_selectedTriple_eq_zero_iff_momentOrientedArea_eq_zero hTN2 h₀₁ h₁₂
      (hsimple.1 i₀) (hsimple.1 i₁) (hsimple.1 i₂),
    momentOrientedArea_eq_orientedArea_matrixMoments]
  change orientedArea (matrixMomentU A) (matrixMomentV A) i.val (i.val + 1)
      (i.val + 2) = 0 ↔ _
  exact orientedArea_consecutive_eq_zero_iff _ _
    (matrixMomentU_strictlyIncreasingUpTo hTN2 hsimple (by omega) (by omega))
    (matrixMomentU_strictlyIncreasingUpTo hTN2 hsimple (by omega) (by omega))

/-- Consecutive maximal minors recover the slope-equality pattern exactly. -/
theorem consecutiveMinorZeroPattern_eq_slopeEqualityPattern
    {A : Matrix (Fin 3) (Fin n) ℝ} (hTN2 : TNUpTo A 2)
    (hsimple : IsSimpleNonloopConfiguration A) :
    consecutiveMinorZeroPattern A = slopeEqualityPattern A := by
  ext i
  simp only [mem_consecutiveMinorZeroPattern_iff, mem_slopeEqualityPattern_iff]
  exact consecutiveMinor_eq_zero_iff_adjacentSlope_eq hTN2 hsimple i

/-- Constancy of a finite slope run is equivalent to equality at every adjacent comparison in
that run. -/
theorem slopesConstantBetween_iff_adjacent {s : ℕ → ℝ} {i k : ℕ} :
    (∀ {t : ℕ}, i ≤ t → t < k → s t = s i) ↔
      ∀ {t : ℕ}, i ≤ t → t + 1 < k → s t = s (t + 1) := by
  constructor
  · intro h t hit htk
    exact (h hit (by omega)).trans (h (by omega) htk).symm
  · intro h t hit htk
    induction t, hit using Nat.le_induction with
    | base => rfl
    | succ t hit ih =>
      exact (h hit (by omega)).symm.trans (ih (by omega))

/-- Equality of adjacent-comparison patterns transports constancy of every valid slope run. -/
theorem slopesConstantBetween_iff_of_pattern_eq
    {A B : Matrix (Fin 3) (Fin n) ℝ} (hpattern : slopeEqualityPattern A = slopeEqualityPattern B)
    {i k : ℕ} (hkn : k < n) :
    SlopesConstantBetween (matrixMomentU A) (matrixMomentV A) i k ↔
      SlopesConstantBetween (matrixMomentU B) (matrixMomentV B) i k := by
  unfold SlopesConstantBetween
  rw [slopesConstantBetween_iff_adjacent, slopesConstantBetween_iff_adjacent]
  constructor <;> intro h t hit htk
  · have ht : t < n - 2 := by omega
    have hmem : (⟨t, ht⟩ : Fin (n - 2)) ∈ slopeEqualityPattern A :=
      (mem_slopeEqualityPattern_iff A ⟨t, ht⟩).2 (h hit htk)
    rw [hpattern] at hmem
    exact (mem_slopeEqualityPattern_iff B ⟨t, ht⟩).1 hmem
  · have ht : t < n - 2 := by omega
    have hmem : (⟨t, ht⟩ : Fin (n - 2)) ∈ slopeEqualityPattern B :=
      (mem_slopeEqualityPattern_iff B ⟨t, ht⟩).2 (h hit htk)
    rw [← hpattern] at hmem
    exact (mem_slopeEqualityPattern_iff A ⟨t, ht⟩).1 hmem

/-- In the simple totally nonnegative region, the equality pattern determines the vanishing of
every ordered maximal minor. -/
theorem maximalMinorZeroSupport_eq_of_slopeEqualityPattern_eq
    {A B : Matrix (Fin 3) (Fin n) ℝ}
    (hATN2 : TNUpTo A 2) (hBTN2 : TNUpTo B 2)
    (hAsimple : IsSimpleNonloopConfiguration A) (hBsimple : IsSimpleNonloopConfiguration B)
    (hATN : TotallyNonnegative A) (hBTN : TotallyNonnegative B)
    (hpattern : slopeEqualityPattern A = slopeEqualityPattern B)
    (cols : Fin 3 ↪o Fin n) :
    orderedMinor A (allRows 3) cols = 0 ↔ orderedMinor B (allRows 3) cols = 0 := by
  have hAσ : SlopesMonotoneUpTo (matrixMomentU A) (matrixMomentV A) n :=
    (totallyNonnegative_iff_momentSlopesMonotone hATN2 hAsimple).1 hATN
  have hBσ : SlopesMonotoneUpTo (matrixMomentU B) (matrixMomentV B) n :=
    (totallyNonnegative_iff_momentSlopesMonotone hBTN2 hBsimple).1 hBTN
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  rw [← selectedTripleEmbedding_eq cols,
    orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween hATN2 hAsimple hAσ h01 h12,
    orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween hBTN2 hBsimple hBσ h01 h12]
  exact slopesConstantBetween_iff_of_pattern_eq hpattern (cols 2).isLt

/-- Conversely, equality of maximal-minor zero support forces equality of the adjacent slope
pattern; consecutive triples already detect every comparison. -/
theorem slopeEqualityPattern_eq_of_maximalMinorZeroSupport_eq
    {A B : Matrix (Fin 3) (Fin n) ℝ}
    (hATN2 : TNUpTo A 2) (hBTN2 : TNUpTo B 2)
    (hAsimple : IsSimpleNonloopConfiguration A) (hBsimple : IsSimpleNonloopConfiguration B)
    (hsupport : ∀ cols : Fin 3 ↪o Fin n,
      (orderedMinor A (allRows 3) cols = 0 ↔ orderedMinor B (allRows 3) cols = 0)) :
    slopeEqualityPattern A = slopeEqualityPattern B := by
  rw [← consecutiveMinorZeroPattern_eq_slopeEqualityPattern hATN2 hAsimple,
    ← consecutiveMinorZeroPattern_eq_slopeEqualityPattern hBTN2 hBsimple]
  ext i
  simp only [mem_consecutiveMinorZeroPattern_iff]
  exact hsupport (strictConsecutiveTripleEmbedding i)

/-- The equality-pattern encoding is injective on maximal-minor supports in the strict region. -/
theorem slopeEqualityPattern_eq_iff_maximalMinorZeroSupport_eq
    {A B : Matrix (Fin 3) (Fin n) ℝ}
    (hATN2 : TNUpTo A 2) (hBTN2 : TNUpTo B 2)
    (hAsimple : IsSimpleNonloopConfiguration A) (hBsimple : IsSimpleNonloopConfiguration B)
    (hATN : TotallyNonnegative A) (hBTN : TotallyNonnegative B) :
    slopeEqualityPattern A = slopeEqualityPattern B ↔
      ∀ cols : Fin 3 ↪o Fin n,
        (orderedMinor A (allRows 3) cols = 0 ↔ orderedMinor B (allRows 3) cols = 0) :=
  ⟨fun h cols ↦ maximalMinorZeroSupport_eq_of_slopeEqualityPattern_eq
      hATN2 hBTN2 hAsimple hBsimple hATN hBTN h cols,
    slopeEqualityPattern_eq_of_maximalMinorZeroSupport_eq hATN2 hBTN2 hAsimple hBsimple⟩

/-- The support-classification theorem specialized to matrices in the strict order-two region. -/
theorem strictRegion_slopeEqualityPattern_eq_iff_maximalMinorZeroSupport_eq
    {A B : Matrix (Fin 3) (Fin n) ℝ}
    (hA : InStrictOrderTwoRegion A) (hB : InStrictOrderTwoRegion B)
    (hATN : TotallyNonnegative A) (hBTN : TotallyNonnegative B) :
    slopeEqualityPattern A = slopeEqualityPattern B ↔
      ∀ cols : Fin 3 ↪o Fin n,
        (orderedMinor A (allRows 3) cols = 0 ↔ orderedMinor B (allRows 3) cols = 0) :=
  slopeEqualityPattern_eq_iff_maximalMinorZeroSupport_eq hA.tnUpTo_two hB.tnUpTo_two
    hA.isSimpleNonloopConfiguration hB.isSimpleNonloopConfiguration hATN hBTN

/-- If every ordered maximal minor of a three-row matrix vanishes, its matrix rank is at most
two. -/
theorem matrixRank_le_two_of_all_orderedMaximalMinors_zero
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hzero : ∀ cols : Fin 3 ↪o Fin n, orderedMinor A (allRows 3) cols = 0) :
    A.rank ≤ 2 := by
  by_contra hrank
  have hrankLe : A.rank ≤ 3 := by
    simpa using A.rank_le_card_height
  have hrankEq : A.rank = 3 := by omega
  obtain ⟨b, hbuniv, _, hspan, hlin⟩ :=
    exists_linearIndepOn_extension (linearIndepOn_empty ℝ A.col)
      (Set.empty_subset (Set.univ : Set (Fin n)))
  have hspan' : Set.range A.col ⊆ Submodule.span ℝ (A.col '' b) := by
    simpa only [Set.image_univ] using hspan
  have hspanEq : Submodule.span ℝ (A.col '' b) = Submodule.span ℝ (Set.range A.col) :=
    le_antisymm (Submodule.span_mono (Set.image_subset_range A.col b))
      (Submodule.span_le.mpr hspan')
  let hbfin : b.Finite := Set.toFinite b
  letI := hbfin.fintype
  have hrankb : Module.finrank ℝ (Submodule.span ℝ (A.col '' b)) = b.ncard := by
    have hrange : Set.range (fun x : b ↦ A.col x) = A.col '' b := by
      ext x
      simp
    rw [← hrange, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact finrank_span_eq_card hlin
  have hbcard : b.ncard = 3 := by
    rw [hspanEq, ← A.rank_eq_finrank_span_cols, hrankEq] at hrankb
    exact hrankb.symm
  let s : Finset (Fin n) := hbfin.toFinset
  have hscard : s.card = 3 := by
    rw [← Set.ncard_eq_toFinset_card b hbfin]
    exact hbcard
  let cols : Fin 3 ↪o Fin n := s.orderEmbOfFin hscard
  have hcolsRange : Set.range cols = b := by
    dsimp only [cols]
    rw [Finset.range_orderEmbOfFin]
    dsimp only [s]
    exact hbfin.coe_toFinset
  have hind : (columnMatroid A).Indep (Set.range cols) := by
    rw [hcolsRange, columnMatroid_indep_iff]
    exact hlin
  have hdet : orderedMinor A (allRows 3) cols ≠ 0 :=
    (orderedMinor_ne_zero_iff_linearIndependent_columns A cols).2
      ((columnMatroid_indep_range_iff A cols).1 hind)
  exact hdet (hzero cols)

/-- If every adjacent slope comparison is an equality, every maximal minor vanishes. -/
theorem all_orderedMaximalMinors_zero_of_allEqualPattern
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTN2 : TNUpTo A 2) (hsimple : IsSimpleNonloopConfiguration A)
    (hTN : TotallyNonnegative A)
    (hpattern : slopeEqualityPattern A = (Finset.univ : Finset (Fin (n - 2)))) :
    ∀ cols : Fin 3 ↪o Fin n, orderedMinor A (allRows 3) cols = 0 := by
  have hσ : SlopesMonotoneUpTo (matrixMomentU A) (matrixMomentV A) n :=
    (totallyNonnegative_iff_momentSlopesMonotone hTN2 hsimple).1 hTN
  intro cols
  have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
  have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
  rw [← selectedTripleEmbedding_eq cols,
    orderedMinor_selectedTriple_eq_zero_iff_slopesConstantBetween hTN2 hsimple hσ h01 h12]
  unfold SlopesConstantBetween
  rw [slopesConstantBetween_iff_adjacent]
  intro t hit htk
  have ht : t < n - 2 := by omega
  have hmem : (⟨t, ht⟩ : Fin (n - 2)) ∈ slopeEqualityPattern A := by
    rw [hpattern]
    simp
  exact (mem_slopeEqualityPattern_iff A ⟨t, ht⟩).1 hmem

/-- The all-equality pattern forces matrix rank at most two. -/
theorem matrixRank_le_two_of_allEqualPattern
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTN2 : TNUpTo A 2) (hsimple : IsSimpleNonloopConfiguration A)
    (hTN : TotallyNonnegative A)
    (hpattern : slopeEqualityPattern A = (Finset.univ : Finset (Fin (n - 2)))) :
    A.rank ≤ 2 :=
  matrixRank_le_two_of_all_orderedMaximalMinors_zero
    (all_orderedMaximalMinors_zero_of_allEqualPattern hTN2 hsimple hTN hpattern)

/-- In the strict order-two region, the all-equality pattern is precisely the excluded
rank-at-most-two case. -/
theorem strictRegion_matrixRank_le_two_of_allEqualPattern
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : InStrictOrderTwoRegion A) (hTN : TotallyNonnegative A)
    (hpattern : slopeEqualityPattern A = (Finset.univ : Finset (Fin (n - 2)))) :
    A.rank ≤ 2 :=
  matrixRank_le_two_of_allEqualPattern hA.tnUpTo_two hA.isSimpleNonloopConfiguration
    hTN hpattern

/-- A full-row-rank matrix in the strict region cannot have the all-equality pattern. -/
theorem slopeEqualityPattern_ne_univ_of_fullRowRank
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hTN2 : TNUpTo A 2) (hsimple : IsSimpleNonloopConfiguration A)
    (hTN : TotallyNonnegative A) (hrank : HasFullRowRank A) :
    slopeEqualityPattern A ≠ (Finset.univ : Finset (Fin (n - 2))) := by
  intro hpattern
  obtain ⟨cols, hcols⟩ := hrank
  exact hcols (all_orderedMaximalMinors_zero_of_allEqualPattern
    hTN2 hsimple hTN hpattern cols)

/-- The all-equality pattern. -/
def allEqualPattern (n : ℕ) : Finset (Fin (n - 2)) := Finset.univ

/-- The finite family of patterns other than the all-equality pattern. -/
def fullRankEqualityPatterns (n : ℕ) : Finset (Finset (Fin (n - 2))) :=
  (Finset.univ : Finset (Fin (n - 2))).powerset.erase (allEqualPattern n)

@[simp]
theorem mem_fullRankEqualityPatterns_iff {P : Finset (Fin (n - 2))} :
    P ∈ fullRankEqualityPatterns n ↔ P ≠ allEqualPattern n := by
  simp [fullRankEqualityPatterns, allEqualPattern]

/-- Every full-row-rank matrix in the strict region has one of the non-all-equal pattern codes. -/
theorem slopeEqualityPattern_mem_fullRankEqualityPatterns
    {A : Matrix (Fin 3) (Fin n) ℝ}
    (hA : InStrictOrderTwoRegion A) (hTN : TotallyNonnegative A)
    (hrank : HasFullRowRank A) :
    slopeEqualityPattern A ∈ fullRankEqualityPatterns n := by
  rw [mem_fullRankEqualityPatterns_iff]
  exact slopeEqualityPattern_ne_univ_of_fullRowRank hA.tnUpTo_two
    hA.isSimpleNonloopConfiguration hTN hrank

/-- There are exactly `2^(n-2)-1` non-all-equal adjacent-comparison patterns. -/
theorem card_fullRankEqualityPatterns :
    (fullRankEqualityPatterns n).card = 2 ^ (n - 2) - 1 := by
  rw [fullRankEqualityPatterns, Finset.card_erase_of_mem (by simp [allEqualPattern]),
    Finset.card_powerset]
  simp

end

end ToeplitzPositroids.RankThree
