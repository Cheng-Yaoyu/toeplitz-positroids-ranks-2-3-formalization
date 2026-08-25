import ToeplitzPositroids.Edrei.TableauBetaPath
import ToeplitzPositroids.Edrei.AlphaNetwork

/-!
# The alpha-side row reconstruction

This file records the row-level inverse construction for the alpha blocks.  An alpha entry `e`
belongs to the network block `e.rev`; cells with smaller block index are crossed earlier in the
network.  The construction is deliberately stated at the level of one row first, which isolates
the arithmetic needed before proving the global vertex-disjointness statement.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

abbrev AlphaRowCell {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) :=
  {c : Fin N // c ∈ S.rowCells a}

def alphaRowBlock {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (c : AlphaRowCell T a) : Fin p :=
  (T.entry ⟨(a, c.val), by
    simpa [FiniteSkewShape.rowCells] using c.property⟩).rev

def alphaRowBlockCount {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) : ℕ :=
  (Finset.univ.filter fun c : AlphaRowCell T a => alphaRowBlock T a c = i).card

def alphaRowPrefixCount {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) : ℕ :=
  (Finset.univ.filter fun c : AlphaRowCell T a => alphaRowBlock T a c < i).card

@[simp]
theorem alphaRowPrefixCount_zero
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (hp : 0 < p) :
    alphaRowPrefixCount T a (⟨0, hp⟩ : Fin p) = 0 := by
  unfold alphaRowPrefixCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro c hc
  intro hbad
  exact Nat.not_lt_zero _ hbad

def alphaRowPrefixCountExt {r N p : ℕ} {S : FiniteSkewShape r N}
  (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin (p + 1)) : ℕ :=
  (Finset.univ.filter fun c : AlphaRowCell T a =>
    (alphaRowBlock T a c).castSucc < i).card

theorem alphaRowCell_card {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) :
    Fintype.card (AlphaRowCell T a) = S.rowWidth a := by
  rw [Fintype.card_subtype]
  simp [FiniteSkewShape.rowCells, FiniteSkewShape.rowWidth]

theorem alphaRowPrefixCountExt_castSucc
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) :
    alphaRowPrefixCountExt T a i.castSucc = alphaRowPrefixCount T a i := by
  rfl

theorem alphaRowPrefixCountExt_le_rowWidth
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin (p + 1)) :
    alphaRowPrefixCountExt T a i ≤ S.rowWidth a := by
  unfold alphaRowPrefixCountExt
  have hcard : (Finset.univ.filter fun c : AlphaRowCell T a =>
      (alphaRowBlock T a c).castSucc < i).card ≤
      (Finset.univ : Finset (AlphaRowCell T a)).card :=
    Finset.card_filter_le _ _
  rw [show (Finset.univ : Finset (AlphaRowCell T a)).card = S.rowWidth a by
    simpa only [Finset.card_univ] using alphaRowCell_card T a] at hcard
  exact hcard

theorem alphaRowPrefixCountExt_last
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) :
    alphaRowPrefixCountExt T a (Fin.last p) = S.rowWidth a := by
  unfold alphaRowPrefixCountExt
  have hfilter : (Finset.univ.filter fun c : AlphaRowCell T a =>
      (alphaRowBlock T a c).castSucc < Fin.last p) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    exact (alphaRowBlock T a c).isLt
  rw [hfilter]
  simpa only [Finset.card_univ] using alphaRowCell_card T a

theorem alphaRowBlock_le_of_col_le {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    {c d : AlphaRowCell T a} (hcd : c.val ≤ d.val) :
    alphaRowBlock T a d ≤ alphaRowBlock T a c := by
  unfold alphaRowBlock
  apply Fin.rev_le_rev.mpr
  exact T.row_weak rfl hcd

theorem alphaRowPrefixCount_add_blockCount_le_rowWidth
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) :
    alphaRowPrefixCount T a i + alphaRowBlockCount T a i ≤ S.rowWidth a := by
  let U : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c < i
  let V : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c = i
  have hdisj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro c hcU hcV
    exact (Finset.mem_filter.mp hcU).2.ne (Finset.mem_filter.mp hcV).2
  have hsub : U ∪ V ⊆ (Finset.univ : Finset (AlphaRowCell T a)) := by
    intro c hc
    simp
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hcard
  have htotal : (Finset.univ : Finset (AlphaRowCell T a)).card = S.rowWidth a := by
    simpa only [Finset.card_univ] using alphaRowCell_card T a
  simpa [U, V, alphaRowPrefixCount, alphaRowBlockCount, htotal] using hcard

theorem alphaRowPrefixCount_le_rowWidth
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) :
    alphaRowPrefixCount T a i ≤ S.rowWidth a := by
  exact (Nat.le_add_right _ _).trans (alphaRowPrefixCount_add_blockCount_le_rowWidth T a i)

theorem alphaRowPrefixCount_add_blockCount_eq_card_filter_le
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) :
    alphaRowPrefixCount T a i + alphaRowBlockCount T a i =
      (Finset.univ.filter fun c : AlphaRowCell T a => alphaRowBlock T a c ≤ i).card := by
  let U : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c < i
  let V : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c = i
  have hU : (Finset.univ.filter fun c : AlphaRowCell T a => alphaRowBlock T a c ≤ i) = U ∪ V := by
    ext c
    simp only [U, V, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  have hdisj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro c hcU hcV
    exact (Finset.mem_filter.mp hcU).2.ne (Finset.mem_filter.mp hcV).2
  rw [hU, Finset.card_union_of_disjoint hdisj]
  rfl

theorem alphaRowBlockCount_le_rowWidth
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p) :
    alphaRowBlockCount T a i ≤ S.rowWidth a := by
  exact (Nat.le_add_left _ _).trans (alphaRowPrefixCount_add_blockCount_le_rowWidth T a i)

theorem alphaRowPrefixCount_succ
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r) (i : Fin p)
    (hi : i.val + 1 < p) :
    alphaRowPrefixCount T a (⟨i.val + 1, hi⟩ : Fin p) =
      alphaRowPrefixCount T a i + alphaRowBlockCount T a i := by
  let j : Fin p := ⟨i.val + 1, hi⟩
  let U : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c < i
  let V : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c = i
  have hU : (Finset.univ.filter fun c : AlphaRowCell T a =>
      alphaRowBlock T a c < j) = U ∪ V := by
    ext c
    simp only [U, V, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    change alphaRowBlock T a c < j ↔
      alphaRowBlock T a c < i ∨ alphaRowBlock T a c = i
    dsimp [j]
    change (alphaRowBlock T a c).val < i.val + 1 ↔
      (alphaRowBlock T a c).val < i.val ∨ alphaRowBlock T a c = i
    have hlt := (alphaRowBlock T a c).isLt
    omega
  have hdisj : Disjoint U V := by
    rw [Finset.disjoint_left]
    intro c hcU hcV
    exact (Finset.mem_filter.mp hcU).2.ne (Finset.mem_filter.mp hcV).2
  unfold alphaRowPrefixCount alphaRowBlockCount
  change (Finset.univ.filter fun c : AlphaRowCell T a =>
    alphaRowBlock T a c < j).card =
      (Finset.univ.filter fun c : AlphaRowCell T a =>
        alphaRowBlock T a c < i).card +
      (Finset.univ.filter fun c : AlphaRowCell T a =>
        alphaRowBlock T a c = i).card
  rw [hU, Finset.card_union_of_disjoint hdisj]

theorem alphaBlockPosition_move_spec {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (t : Fin (finiteFactorStageCount 1 0 N))
    (hmove :
      (alphaBlockPosition source d hd t.succ).val =
        (alphaBlockPosition source d hd t.castSucc).val + 1) :
    (alphaBlockPosition source d hd t.castSucc).val = t.val := by
  have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
  unfold alphaBlockPosition at hmove ⊢
  by_cases hsource : source.val ≤ t.val
  · by_cases hdone : d ≤ t.val - source.val
    · have hnextsource : source.val ≤ t.val + 1 := by omega
      have hdone_next : d ≤ t.val + 1 - source.val := by omega
      change source.val + (if source.val ≤ t.val + 1 then
        min d (t.val + 1 - source.val) else 0) =
        source.val + (if source.val ≤ t.val then
          min d (t.val - source.val) else 0) + 1 at hmove
      simp [hsource, hnextsource, hdone, hdone_next] at hmove
    · have hbefore : t.val - source.val < d := Nat.lt_of_not_ge hdone
      have hnextsource : source.val ≤ t.val + 1 := by omega
      change source.val + (if source.val ≤ t.val + 1 then
        min d (t.val + 1 - source.val) else 0) =
        source.val + (if source.val ≤ t.val then
          min d (t.val - source.val) else 0) + 1 at hmove
      change source.val + (if source.val ≤ t.val then
        min d (t.val - source.val) else 0) = t.val
      simp only [if_pos hsource, if_pos hnextsource] at hmove ⊢
      rw [Nat.min_eq_right (Nat.le_of_lt hbefore)] at hmove
      rw [Nat.min_eq_right (by omega : t.val + 1 - source.val ≤ d)] at hmove
      rw [Nat.min_eq_right (Nat.le_of_lt hbefore)]
      omega
  · have hnextsource : ¬source.val ≤ t.val + 1 ∨ source.val = t.val + 1 := by omega
    rcases hnextsource with hnext | hnext
    · simp [hsource, hnext] at hmove
    · simp [hsource, hnext] at hmove

def alphaRowBlockSource {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) : Fin (N + 1) :=
  ⟨boundary.val + alphaRowPrefixCount T a i, by
    have hp := alphaRowPrefixCount_le_rowWidth T a i
    omega⟩

theorem alphaRowBlockSource_add_count_le
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) :
    (alphaRowBlockSource T a boundary hbound i).val +
        alphaRowBlockCount T a i ≤ N := by
  unfold alphaRowBlockSource
  change boundary.val + alphaRowPrefixCount T a i + alphaRowBlockCount T a i ≤ N
  have hcnt := alphaRowPrefixCount_add_blockCount_le_rowWidth T a i
  omega

theorem alphaRowBlockSource_zero
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) :
    boundary.val ≤ (alphaRowBlockSource T a boundary hbound i).val := by
  unfold alphaRowBlockSource
  change boundary.val ≤ boundary.val + alphaRowPrefixCount T a i
  omega

@[simp]
theorem alphaRowBlockSource_succ
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) (hi : i.val + 1 < p) :
    alphaRowBlockSource T a boundary hbound
        (⟨i.val + 1, hi⟩ : Fin p) =
      ⟨(alphaRowBlockSource T a boundary hbound i).val +
        alphaRowBlockCount T a i, by
          have h := alphaRowBlockSource_add_count_le T a boundary hbound i
          omega⟩ := by
  apply Fin.ext
  unfold alphaRowBlockSource
  have hprefix := alphaRowPrefixCount_succ T a i hi
  change boundary.val + alphaRowPrefixCount T a (⟨i.val + 1, hi⟩ : Fin p) =
    boundary.val + alphaRowPrefixCount T a i + alphaRowBlockCount T a i
  rw [hprefix]
  omega

theorem alphaRowPrefixCount_add_blockCount_last
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (i : Fin p) (hi : i.val + 1 = p) :
    alphaRowPrefixCount T a i + alphaRowBlockCount T a i = S.rowWidth a := by
  have hcard := alphaRowPrefixCount_add_blockCount_eq_card_filter_le T a i
  have hfilter :
      (Finset.univ.filter fun c : AlphaRowCell T a => alphaRowBlock T a c ≤ i) =
        Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    have hblock := (alphaRowBlock T a c).isLt
    change (alphaRowBlock T a c).val ≤ i.val
    omega
  calc
    alphaRowPrefixCount T a i + alphaRowBlockCount T a i =
        (Finset.univ : Finset (AlphaRowCell T a)).card := by
      rw [← hfilter]
      exact hcard
    _ = Fintype.card (AlphaRowCell T a) := Finset.card_univ
    _ = S.rowWidth a := alphaRowCell_card T a

def alphaRowBoundaryPosition {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin (p + 1)) : Fin (N + 1) :=
  ⟨boundary.val + alphaRowPrefixCountExt T a i, by
    have hi := alphaRowPrefixCountExt_le_rowWidth T a i
    omega⟩

@[simp]
theorem alphaRowBoundaryPosition_castSucc
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) :
    alphaRowBoundaryPosition T a boundary hbound i.castSucc =
      alphaRowBlockSource T a boundary hbound i := by
  apply Fin.ext
  unfold alphaRowBoundaryPosition alphaRowBlockSource
  change boundary.val + alphaRowPrefixCountExt T a i.castSucc =
    boundary.val + alphaRowPrefixCount T a i
  rw [alphaRowPrefixCountExt_castSucc]

@[simp]
theorem alphaRowBoundaryPosition_last
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N) :
    alphaRowBoundaryPosition T a boundary hbound (Fin.last p) =
      ⟨boundary.val + S.rowWidth a, by omega⟩ := by
  apply Fin.ext
  unfold alphaRowBoundaryPosition
  change boundary.val + alphaRowPrefixCountExt T a (Fin.last p) =
    boundary.val + S.rowWidth a
  rw [alphaRowPrefixCountExt_last]

theorem alphaRowBoundaryPosition_monotone
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N) :
    Monotone (alphaRowBoundaryPosition T a boundary hbound) := by
  intro i j hij
  apply Fin.mk_le_mk.mpr
  change boundary.val + alphaRowPrefixCountExt T a i ≤
    boundary.val + alphaRowPrefixCountExt T a j
  apply Nat.add_le_add_left
  unfold alphaRowPrefixCountExt
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter] at hc ⊢
  exact ⟨hc.1, lt_of_lt_of_le hc.2 hij⟩

theorem alphaRowBlockCount_one
    {r N : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S 1) (a : Fin r) :
    alphaRowBlockCount T a 0 = S.rowWidth a := by
  unfold alphaRowBlockCount
  have hfilter : (Finset.univ.filter fun c : AlphaRowCell T a =>
      alphaRowBlock T a c = 0) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    apply Fin.eq_zero
  rw [hfilter]
  simpa only [Finset.card_univ] using alphaRowCell_card T a

def alphaRowBlockPosition {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) (k : Fin (N + 1)) : Fin (N + 1) :=
  alphaBlockPosition (alphaRowBlockSource T a boundary hbound i)
    (alphaRowBlockCount T a i)
    (alphaRowBlockSource_add_count_le T a boundary hbound i)
    ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩

@[simp]
theorem alphaRowBlockPosition_zero
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) :
    alphaRowBlockPosition T a boundary hbound i 0 =
      alphaRowBlockSource T a boundary hbound i := by
  apply Fin.ext
  unfold alphaRowBlockPosition alphaBlockPosition
  simp [alphaRowBlockSource]

@[simp]
theorem alphaRowBlockPosition_last
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) :
    alphaRowBlockPosition T a boundary hbound i (Fin.last N) =
      ⟨(alphaRowBlockSource T a boundary hbound i).val +
        alphaRowBlockCount T a i, by
        have h := alphaRowBlockSource_add_count_le T a boundary hbound i
        omega⟩ := by
  apply Fin.ext
  unfold alphaRowBlockPosition alphaBlockPosition
  simp only [Fin.last, Fin.val_mk]
  have hcount := alphaRowBlockSource_add_count_le T a boundary hbound i
  have hi : (alphaRowBlockSource T a boundary hbound i).val ≤ N := by omega
  have hd : alphaRowBlockCount T a i ≤
      N - (alphaRowBlockSource T a boundary hbound i).val :=
    Nat.le_sub_of_add_le (by omega)
  simp [hi, Nat.min_eq_left hd]

theorem alphaRowBlockPosition_step
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) (k : Fin N) :
    (alphaRowBlockPosition T a boundary hbound i k.succ).val =
        (alphaRowBlockPosition T a boundary hbound i k.castSucc).val ∨
      (alphaRowBlockPosition T a boundary hbound i k.succ).val =
        (alphaRowBlockPosition T a boundary hbound i k.castSucc).val + 1 := by
  unfold alphaRowBlockPosition
  exact alphaBlockPosition_step
    (alphaRowBlockSource T a boundary hbound i)
    (alphaRowBlockCount T a i)
    (alphaRowBlockSource_add_count_le T a boundary hbound i)
    ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩

theorem alphaRowBlockPosition_network_step
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) (k : Fin N) :
    NetworkStepAllowed 1 0 N k.val
      (alphaRowBlockPosition T a boundary hbound i k.castSucc)
      (alphaRowBlockPosition T a boundary hbound i k.succ) := by
  have hstep := alphaRowBlockPosition_step T a boundary hbound i k
  unfold NetworkStepAllowed
  rw [if_neg (by omega : ¬k.val < 0)]
  rcases hstep with hstay | hmove
  · left
    exact hstay
  · right
    have hmove' := alphaBlockPosition_move_spec
      (alphaRowBlockSource T a boundary hbound i)
      (alphaRowBlockCount T a i)
      (alphaRowBlockSource_add_count_le T a boundary hbound i)
      ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
      (by simpa [alphaRowBlockPosition] using hmove)
    have hN : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      have hk := k.isLt
      simp at hk
    have hdiv : k.val / N = 0 := Nat.div_eq_of_lt k.isLt
    have hmod : k.val % N = k.val := Nat.mod_eq_of_lt k.isLt
    refine ⟨by simp, ?_⟩
    constructor
    · simpa [alphaRowBlockPosition, hmod] using hmove'
    · exact hmove

noncomputable def alphaRowPath_one
    {r N : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData 1 0) (T : AlphaSkewTableau S 1) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N) :
    FiniteFactorPath D N boundary
      (⟨boundary.val + S.rowWidth a, by omega⟩ : Fin (N + 1)) := by
  refine alphaBlockPath D ?_
  change boundary.val ≤ boundary.val + S.rowWidth a
  omega

/-! The global path position is added after the row-level block arithmetic has been completed. -/

end

end ToeplitzPositroids.Edrei
