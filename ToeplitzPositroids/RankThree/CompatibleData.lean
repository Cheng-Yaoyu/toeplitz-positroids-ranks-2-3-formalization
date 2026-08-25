import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-!
# Compatible rank-three Toeplitz data

This file gives a numeric, canonical version of Definition 12. The raw ground set is `Fin n`.
It is partitioned, from left to right, into initial loops, an initial parallel class, singleton
simplified classes, a terminal parallel class, and terminal loops. Prescribed rank-two flats are
closed ordinary intervals in the simplified ground set.
-/

namespace ToeplitzPositroids

/-- A closed ordinary interval in the finite linear order `Fin m`. -/
structure SimplifiedInterval (m : ℕ) where
  /-- The first point of the interval. -/
  left : Fin m
  /-- The last point of the interval. -/
  right : Fin m
  /-- The endpoints occur in their displayed order. -/
  left_le_right : left ≤ right
  deriving DecidableEq

namespace SimplifiedInterval

/-- The finite set of points in a simplified ordinary interval. -/
def points {m : ℕ} (H : SimplifiedInterval m) : Finset (Fin m) :=
  Finset.Icc H.left H.right

@[simp]
theorem mem_points {m : ℕ} {H : SimplifiedInterval m} {x : Fin m} :
    x ∈ H.points ↔ H.left ≤ x ∧ x ≤ H.right :=
  Finset.mem_Icc

@[simp]
theorem left_mem_points {m : ℕ} (H : SimplifiedInterval m) : H.left ∈ H.points := by
  simp [points, H.left_le_right]

@[simp]
theorem right_mem_points {m : ℕ} (H : SimplifiedInterval m) : H.right ∈ H.points := by
  simp [points, H.left_le_right]

/-- The number of points in a closed interval of `Fin m`. -/
theorem card_points {m : ℕ} (H : SimplifiedInterval m) :
    H.points.card = H.right.val + 1 - H.left.val := by
  exact Fin.card_Icc H.left H.right

end SimplifiedInterval

/-- Canonical compatible rank-three Toeplitz data on a ground set of size `n`.

The displayed cardinality equation fixes the five raw blocks uniquely. The `simplifiedSize - 2`
middle elements are singleton parallel classes; the two endpoint classes account for the first
and last simplified elements. -/
structure CompatibleRankThreeData (n : ℕ) where
  /-- Number of initial loops. -/
  leftLoopCount : ℕ
  /-- Number of terminal loops. -/
  rightLoopCount : ℕ
  /-- Size of the initial nonloop parallel class. -/
  initialParallelSize : ℕ
  /-- Size of the terminal nonloop parallel class. -/
  terminalParallelSize : ℕ
  /-- Cardinality of the simplified nonloop ground set. -/
  simplifiedSize : ℕ
  initialParallelSize_pos : 0 < initialParallelSize
  terminalParallelSize_pos : 0 < terminalParallelSize
  simplifiedSize_ge_three : 3 ≤ simplifiedSize
  /-- The raw blocks exhaust the ground set. -/
  groundSize_eq :
    leftLoopCount + initialParallelSize + (simplifiedSize - 2) + terminalParallelSize +
      rightLoopCount = n
  /-- An initial loop block forces the adjacent parallel class to be a singleton. -/
  initialParallel_singleton_of_leftLoops : 0 < leftLoopCount → initialParallelSize = 1
  /-- A terminal loop block forces the adjacent parallel class to be a singleton. -/
  terminalParallel_singleton_of_rightLoops : 0 < rightLoopCount → terminalParallelSize = 1
  /-- The prescribed maximal rank-two ordinary intervals. -/
  intervals : Finset (SimplifiedInterval simplifiedSize)
  /-- Every prescribed interval contains at least three simplified points. -/
  interval_large : ∀ H ∈ intervals, H.left.val + 2 ≤ H.right.val
  /-- Distinct prescribed intervals are disjoint or meet at a common endpoint. -/
  intervals_separated :
    ∀ H ∈ intervals, ∀ K ∈ intervals, H ≠ K →
      H.right < K.left ∨ K.right < H.left ∨ H.right = K.left ∨ K.right = H.left
  /-- A protected initial endpoint lies in no prescribed rank-two interval. -/
  initial_endpoint_protected :
    0 < leftLoopCount ∨ 1 < initialParallelSize →
      ∀ H ∈ intervals, H.left.val ≠ 0
  /-- A protected terminal endpoint lies in no prescribed rank-two interval. -/
  terminal_endpoint_protected :
    0 < rightLoopCount ∨ 1 < terminalParallelSize →
      ∀ H ∈ intervals, H.right.val + 1 ≠ simplifiedSize
  /-- No prescribed rank-two interval is the whole simplified ground set. -/
  interval_not_whole :
    ∀ H ∈ intervals, H.left.val ≠ 0 ∨ H.right.val + 1 ≠ simplifiedSize

namespace CompatibleRankThreeData

variable {n : ℕ} (D : CompatibleRankThreeData n)

/-- First raw index after the initial parallel class. -/
def middleStart : ℕ := D.leftLoopCount + D.initialParallelSize

/-- First raw index of the terminal parallel class. -/
def terminalStart : ℕ := D.middleStart + (D.simplifiedSize - 2)

/-- First raw index of the terminal loop block. -/
def rightLoopStart : ℕ := D.terminalStart + D.terminalParallelSize

theorem rightLoopStart_add_rightLoopCount :
    D.rightLoopStart + D.rightLoopCount = n := by
  change
    D.leftLoopCount + D.initialParallelSize + (D.simplifiedSize - 2) +
      D.terminalParallelSize + D.rightLoopCount = n
  exact D.groundSize_eq

theorem rightLoopStart_le_groundSize : D.rightLoopStart ≤ n := by
  have := D.rightLoopStart_add_rightLoopCount
  omega

/-- Membership in the initial loop block. -/
def IsLeftLoop (j : Fin n) : Prop := j.val < D.leftLoopCount

/-- Membership in the terminal loop block. -/
def IsRightLoop (j : Fin n) : Prop := D.rightLoopStart ≤ j.val

/-- Membership in either canonical loop block. -/
def IsLoop (j : Fin n) : Prop := D.IsLeftLoop j ∨ D.IsRightLoop j

/-- Membership in the canonical nonloop interval. -/
def IsNonloop (j : Fin n) : Prop :=
  D.leftLoopCount ≤ j.val ∧ j.val < D.rightLoopStart

/-- Membership in the initial endpoint parallel class. -/
def IsInitialParallel (j : Fin n) : Prop :=
  D.leftLoopCount ≤ j.val ∧ j.val < D.middleStart

/-- Membership in the terminal endpoint parallel class. -/
def IsTerminalParallel (j : Fin n) : Prop :=
  D.terminalStart ≤ j.val ∧ j.val < D.rightLoopStart

instance decidableIsLeftLoop (j : Fin n) : Decidable (D.IsLeftLoop j) := by
  unfold IsLeftLoop
  infer_instance

instance decidableIsRightLoop (j : Fin n) : Decidable (D.IsRightLoop j) := by
  unfold IsRightLoop
  infer_instance

instance decidableIsLoop (j : Fin n) : Decidable (D.IsLoop j) := by
  unfold IsLoop
  infer_instance

instance decidableIsNonloop (j : Fin n) : Decidable (D.IsNonloop j) := by
  unfold IsNonloop
  infer_instance

instance decidableIsInitialParallel (j : Fin n) : Decidable (D.IsInitialParallel j) := by
  unfold IsInitialParallel
  infer_instance

instance decidableIsTerminalParallel (j : Fin n) : Decidable (D.IsTerminalParallel j) := by
  unfold IsTerminalParallel
  infer_instance

theorem isNonloop_iff_not_isLoop (j : Fin n) : D.IsNonloop j ↔ ¬D.IsLoop j := by
  unfold IsNonloop IsLoop IsLeftLoop IsRightLoop
  omega

theorem isInitialParallel_isNonloop {j : Fin n} (hj : D.IsInitialParallel j) :
    D.IsNonloop j := by
  refine ⟨hj.1, hj.2.trans_le ?_⟩
  change D.middleStart ≤ D.middleStart + (D.simplifiedSize - 2) + D.terminalParallelSize
  exact (Nat.le_add_right D.middleStart (D.simplifiedSize - 2)).trans
    (Nat.le_add_right (D.middleStart + (D.simplifiedSize - 2)) D.terminalParallelSize)

theorem isTerminalParallel_isNonloop {j : Fin n} (hj : D.IsTerminalParallel j) :
    D.IsNonloop j := by
  refine ⟨?_, hj.2⟩
  exact (by
    calc
      D.leftLoopCount ≤ D.middleStart := by simp [middleStart]
      _ ≤ D.terminalStart := by simp [terminalStart]
      _ ≤ j.val := hj.1)

/-- The numeric simplified index of a nonloop raw element. -/
def simplifiedIndexNat (j : Fin n) : ℕ :=
  if j.val < D.middleStart then 0
  else if j.val < D.terminalStart then j.val - D.middleStart + 1
  else D.simplifiedSize - 1

theorem simplifiedIndexNat_lt (j : Fin n) :
    D.simplifiedIndexNat j < D.simplifiedSize := by
  have hm := D.simplifiedSize_ge_three
  unfold simplifiedIndexNat
  split <;> rename_i h₁
  · omega
  split <;> rename_i h₂
  · have hmiddle : D.middleStart ≤ j.val := Nat.le_of_not_gt h₁
    have hdiff : j.val - D.middleStart < D.simplifiedSize - 2 :=
      (Nat.sub_lt_iff_lt_add' hmiddle).2 (by simpa [terminalStart] using h₂)
    omega
  · omega

/-- The numeric simplified index as an element of the simplified ground set. Its value on loops
is irrelevant because `simplifiedIndex?` suppresses it. -/
def simplifiedIndex (j : Fin n) : Fin D.simplifiedSize :=
  ⟨D.simplifiedIndexNat j, D.simplifiedIndexNat_lt j⟩

/-- The partial simplification map, undefined precisely on loops. -/
def simplifiedIndex? (j : Fin n) : Option (Fin D.simplifiedSize) :=
  if D.IsNonloop j then some (D.simplifiedIndex j) else none

@[simp]
theorem simplifiedIndex?_eq_none_iff (j : Fin n) :
    D.simplifiedIndex? j = none ↔ D.IsLoop j := by
  classical
  simp [simplifiedIndex?, D.isNonloop_iff_not_isLoop]

@[simp]
theorem simplifiedIndex?_eq_some {j : Fin n} (hj : D.IsNonloop j) :
    D.simplifiedIndex? j = some (D.simplifiedIndex j) := by
  classical
  simp [simplifiedIndex?, hj]

/-- The set of distinct simplified images of a raw finite set. -/
def simplifiedImages (J : Finset (Fin n)) : Finset (Fin D.simplifiedSize) :=
  J.biUnion fun j ↦ (D.simplifiedIndex? j).toFinset

/-- A raw finite set meets one of the two loop blocks. -/
def MeetsLoops (J : Finset (Fin n)) : Prop :=
  ∃ j ∈ J, D.IsLoop j

/-- A raw finite set contains two elements of the initial parallel class. -/
def ContainsInitialParallelPair (J : Finset (Fin n)) : Prop :=
  2 ≤ (J.filter D.IsInitialParallel).card

/-- A raw finite set contains two elements of the terminal parallel class. -/
def ContainsTerminalParallelPair (J : Finset (Fin n)) : Prop :=
  2 ≤ (J.filter D.IsTerminalParallel).card

/-- A set of simplified points is contained in one prescribed ordinary interval. -/
def SimplifiedCollinear (X : Finset (Fin D.simplifiedSize)) : Prop :=
  ∃ H ∈ D.intervals, X ⊆ H.points

/-- The collinearity nonbasis rule on an actual triple of simplified points. -/
def SimplifiedTripleNonbasis (T : Finset (Fin D.simplifiedSize)) : Prop :=
  T.card = 3 ∧ D.SimplifiedCollinear T

/-- A simplified set of size at least three all of whose triples are collinearity nonbases. -/
def IsSimplifiedRankTwoFlat (X : Finset (Fin D.simplifiedSize)) : Prop :=
  3 ≤ X.card ∧
    ∀ T : Finset (Fin D.simplifiedSize), T ⊆ X → T.card = 3 →
      D.SimplifiedTripleNonbasis T

/-- The triple nonbasis predicate induced by compatible data, including loops, endpoint parallel
pairs, and prescribed collinear intervals. -/
def TripleNonbasis (J : Finset (Fin n)) : Prop :=
  J.card = 3 ∧
    (MeetsLoops D J ∨ ContainsInitialParallelPair D J ∨
      ContainsTerminalParallelPair D J ∨
      (D.simplifiedImages J).card = 3 ∧ D.SimplifiedCollinear (D.simplifiedImages J))

/-- The canonical finite family of bases induced by the triple nonbasis rule. -/
noncomputable def basisFinsets : Finset (Finset (Fin n)) := by
  classical
  exact (Finset.univ.powersetCard 3).filter fun J ↦ ¬D.TripleNonbasis J

@[simp]
theorem mem_basisFinsets_iff {J : Finset (Fin n)} :
    J ∈ basisFinsets D ↔ J.card = 3 ∧ ¬D.TripleNonbasis J := by
  classical
  simp [basisFinsets]

/-- Two prescribed intervals containing two distinct common points are equal. This is the
intersection observation used in the manuscript's maximality argument. -/
theorem interval_eq_of_two_common {H K : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) (hK : K ∈ D.intervals) {x y : Fin D.simplifiedSize}
    (hxy : x ≠ y) (hxH : x ∈ H.points) (hxK : x ∈ K.points)
    (hyH : y ∈ H.points) (hyK : y ∈ K.points) :
    H = K := by
  rw [SimplifiedInterval.mem_points] at hxH hxK hyH hyK
  by_contra hHK
  rcases D.intervals_separated H hH K hK hHK with hsep | hsep | htouch | htouch
  · exact (not_lt_of_ge (hxK.1.trans hxH.2)) hsep
  · exact (not_lt_of_ge (hxH.1.trans hxK.2)) hsep
  · have hx : x = H.right := le_antisymm hxH.2 (htouch ▸ hxK.1)
    have hy : y = H.right := le_antisymm hyH.2 (htouch ▸ hyK.1)
    exact hxy (hx.trans hy.symm)
  · have hx : x = K.right := le_antisymm hxK.2 (htouch ▸ hxH.1)
    have hy : y = K.right := le_antisymm hyK.2 (htouch ▸ hyH.1)
    exact hxy (hx.trans hy.symm)

/-- If every triple of a simplified set with at least three points is a prescribed collinearity
nonbasis, then the whole set lies in one prescribed interval. -/
theorem exists_interval_of_all_triples_nonbasis {X : Finset (Fin D.simplifiedSize)}
    (hXcard : 3 ≤ X.card)
    (htriples : ∀ T : Finset (Fin D.simplifiedSize), T ⊆ X → T.card = 3 →
      D.SimplifiedTripleNonbasis T) :
    ∃ H ∈ D.intervals, X ⊆ H.points := by
  obtain ⟨T, hTX, hTcard⟩ := Finset.exists_subset_card_eq hXcard
  obtain ⟨x₁, x₂, x₃, hx₁₂, hx₁₃, hx₂₃, rfl⟩ := Finset.card_eq_three.mp hTcard
  obtain ⟨H₀, hH₀, hTH₀⟩ := (htriples {x₁, x₂, x₃} hTX (by simp [hx₁₂, hx₁₃, hx₂₃])).2
  refine ⟨H₀, hH₀, fun x hxX ↦ ?_⟩
  by_cases hx₁ : x = x₁
  · subst x
    exact hTH₀ (by simp)
  by_cases hx₂ : x = x₂
  · subst x
    exact hTH₀ (by simp)
  have hpairSubset : ({x, x₁, x₂} : Finset (Fin D.simplifiedSize)) ⊆ X := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hxX
    · exact hTX (by simp)
    · exact hTX (by simp)
  have hpairCard : ({x, x₁, x₂} : Finset (Fin D.simplifiedSize)).card = 3 := by
    simp [hx₁, hx₂, hx₁₂]
  obtain ⟨Hₓ, hHₓ, hpairHₓ⟩ := (htriples {x, x₁, x₂} hpairSubset hpairCard).2
  have hEq : H₀ = Hₓ := D.interval_eq_of_two_common hH₀ hHₓ hx₁₂
    (hTH₀ (by simp)) (hpairHₓ (by simp)) (hTH₀ (by simp)) (hpairHₓ (by simp))
  rw [hEq]
  exact hpairHₓ (by simp)

/-- Every three-point subset of a prescribed interval is a simplified nonbasis. -/
theorem simplifiedTripleNonbasis_of_subset_interval {H : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) {T : Finset (Fin D.simplifiedSize)}
    (hTcard : T.card = 3) (hTH : T ⊆ H.points) :
    D.SimplifiedTripleNonbasis T :=
  ⟨hTcard, H, hH, hTH⟩

/-- Every prescribed interval has at least three points. -/
theorem three_le_card_interval_points {H : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) :
    3 ≤ H.points.card := by
  rw [SimplifiedInterval.card_points]
  apply Nat.le_sub_of_add_le
  have := D.interval_large H hH
  omega

/-- Prescribed intervals are maximal among simplified sets of size at least three all of whose
triples are collinearity nonbases. -/
theorem interval_maximal_for_triple_nonbases {H : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) {X : Finset (Fin D.simplifiedSize)}
    (hHX : H.points ⊆ X)
    (htriples : ∀ T : Finset (Fin D.simplifiedSize), T ⊆ X → T.card = 3 →
      D.SimplifiedTripleNonbasis T) :
    X = H.points := by
  have hXcard : 3 ≤ X.card :=
    (D.three_le_card_interval_points hH).trans (Finset.card_le_card hHX)
  obtain ⟨K, hK, hXK⟩ := D.exists_interval_of_all_triples_nonbasis hXcard htriples
  have hne : H.left ≠ H.right := by
    intro heq
    have := D.interval_large H hH
    omega
  have hHK : H = K := D.interval_eq_of_two_common hH hK hne
    H.left_mem_points (hXK (hHX H.left_mem_points))
    H.right_mem_points (hXK (hHX H.right_mem_points))
  subst K
  exact Finset.Subset.antisymm hXK hHX

/-- Each prescribed interval is maximal among the simplified rank-two-flat candidates. -/
theorem interval_isMaximal_rankTwoFlat {H : SimplifiedInterval D.simplifiedSize}
    (hH : H ∈ D.intervals) :
    Maximal D.IsSimplifiedRankTwoFlat H.points := by
  refine ⟨⟨D.three_le_card_interval_points hH, ?_⟩, ?_⟩
  · intro T hTH hTcard
    exact D.simplifiedTripleNonbasis_of_subset_interval hH hTcard hTH
  · intro X hX hHX
    have hEq := D.interval_maximal_for_triple_nonbases hH hHX hX.2
    simp [hEq]

/-- The prescribed intervals are precisely the maximal simplified subsets of size at least three
whose triples are all nonbases. -/
theorem maximal_rankTwoFlat_iff_eq_interval {X : Finset (Fin D.simplifiedSize)} :
    Maximal D.IsSimplifiedRankTwoFlat X ↔
      ∃ H ∈ D.intervals, X = H.points := by
  constructor
  · intro hX
    obtain ⟨H, hH, hXH⟩ :=
      D.exists_interval_of_all_triples_nonbasis hX.1.1 hX.1.2
    have hHX : H.points ⊆ X := (hX.2 (D.interval_isMaximal_rankTwoFlat hH).1 hXH)
    exact ⟨H, hH, Finset.Subset.antisymm hXH hHX⟩
  · rintro ⟨H, hH, rfl⟩
    exact D.interval_isMaximal_rankTwoFlat hH

end CompatibleRankThreeData

end ToeplitzPositroids
