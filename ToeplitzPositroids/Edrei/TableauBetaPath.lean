import ToeplitzPositroids.Edrei.NetworkTableauBridge

/-!
# Paths reconstructed from beta tableaux

For a beta tableau row, a cell with entry `e` is crossed at the network beta stage `e.rev`.
The position at a vertex is the source wire plus the number of row cells whose reversed entry is
strictly before that vertex.  Row strictness makes the stage labels injective, which is exactly the
fact needed to prove that every network step is either a stay or a single upward move.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

abbrev BetaRowCell {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) :=
  {c : Fin N // c ∈ S.rowCells a}

def betaRowStage {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (c : BetaRowCell T a) : Fin q :=
  (T.entry ⟨(a, c.val), by
    simpa [FiniteSkewShape.rowCells] using c.property⟩).rev

def betaRowMoveCount {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (s : Fin (q + 1)) : ℕ :=
  (Finset.univ.filter fun c : BetaRowCell T a =>
    (betaRowStage T a c).val < s.val).card

theorem betaRowCell_card {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) :
    Fintype.card (BetaRowCell T a) = S.rowWidth a := by
  rw [Fintype.card_subtype]
  simp [FiniteSkewShape.rowCells, FiniteSkewShape.rowWidth]

theorem betaRowMoveCount_le_width {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (s : Fin (q + 1)) :
    betaRowMoveCount T a s ≤ S.rowWidth a := by
  unfold betaRowMoveCount
  calc
    (Finset.univ.filter fun c : BetaRowCell T a =>
        (betaRowStage T a c).val < s.val).card ≤
        (Finset.univ : Finset (BetaRowCell T a)).card :=
      Finset.card_filter_le (Finset.univ : Finset (BetaRowCell T a)) _
    _ = Fintype.card (BetaRowCell T a) := by simp
    _ = S.rowWidth a := betaRowCell_card T a

def betaTableauPosition {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r)
    (source : Fin (N + 1)) (hbound : source.val + S.rowWidth a ≤ N)
    (s : Fin (q + 1)) : Fin (N + 1) :=
  ⟨source.val + betaRowMoveCount T a s, by
    have hc := betaRowMoveCount_le_width T a s
    omega⟩

theorem betaTableauPosition_zero {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r)
    (source : Fin (N + 1)) (hbound : source.val + S.rowWidth a ≤ N) :
    betaTableauPosition T a source hbound 0 = source := by
  apply Fin.ext
  unfold betaTableauPosition betaRowMoveCount
  simp

theorem betaTableauPosition_last {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r)
    (source : Fin (N + 1)) (hbound : source.val + S.rowWidth a ≤ N) :
    betaTableauPosition T a source hbound (Fin.last q) =
      ⟨source.val + S.rowWidth a, by omega⟩ := by
  apply Fin.ext
  change source.val + betaRowMoveCount T a (Fin.last q) =
    source.val + S.rowWidth a
  unfold betaRowMoveCount
  have hfilter : (Finset.univ.filter fun c : BetaRowCell T a =>
      (betaRowStage T a c).val < (Fin.last q).val) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro c hc
    exact (betaRowStage T a c).isLt
  rw [hfilter]
  change source.val + Fintype.card (BetaRowCell T a) =
    source.val + S.rowWidth a
  rw [betaRowCell_card]

theorem betaRowStage_injective {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) :
    Function.Injective (betaRowStage T a) := by
  intro c d hcd
  apply Subtype.ext
  rcases lt_trichotomy c.val d.val with hlt | heq | hgt
  · have hentry := T.row_strict
      (x := ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩)
      (y := ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩) rfl hlt
    have hrev := congrArg Fin.rev hcd
    have hentry_eq : T.entry ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩ =
      T.entry ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩ := by
      simpa [betaRowStage] using hrev
    exact False.elim ((ne_of_lt hentry) hentry_eq)
  · exact heq
  · have hentry := T.row_strict
      (x := ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩)
      (y := ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩) rfl hgt
    have hrev := congrArg Fin.rev hcd
    have hentry_eq : T.entry ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩ =
      T.entry ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩ := by
      simpa [betaRowStage] using hrev
    exact False.elim ((ne_of_lt hentry) hentry_eq.symm)

theorem betaRowMoveCount_step {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (t : Fin q) :
    betaRowMoveCount T a t.succ = betaRowMoveCount T a t.castSucc ∨
      betaRowMoveCount T a t.succ = betaRowMoveCount T a t.castSucc + 1 := by
  let U₀ : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun c => (betaRowStage T a c).val < t.val
  let E : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun c => (betaRowStage T a c).val = t.val
  let U₁ : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun c => (betaRowStage T a c).val < t.succ.val
  have hU : U₁ = U₀ ∪ E := by
    ext c
    simp only [U₁, U₀, E, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union, Fin.val_succ]
    omega
  have hdisj : Disjoint U₀ E := by
    rw [Finset.disjoint_left]
    intro c hc0 hce
    have hc0' := (Finset.mem_filter.mp hc0).2
    have hce' := (Finset.mem_filter.mp hce).2
    omega
  have hcardE : E.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro c hc d hd
    apply Subtype.ext
    have hstage : betaRowStage T a c = betaRowStage T a d := by
      apply Fin.ext
      have hc' := (Finset.mem_filter.mp hc).2
      have hd' := (Finset.mem_filter.mp hd).2
      omega
    exact congrArg Subtype.val ((betaRowStage_injective T a) hstage)
  have hcardE' : E.card = 0 ∨ E.card = 1 := by omega
  have hcard := Finset.card_union_of_disjoint hdisj
  change U₁.card = U₀.card ∨ U₁.card = U₀.card + 1
  rw [hU, hcard]
  rcases hcardE' with hzero | hone
  · left
    omega
  · right
    omega

noncomputable def betaTableauPath {r N q : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData 0 q) (T : BetaSkewTableau S q) (a : Fin r)
    {source sink : Fin (N + 1)}
    (hsum : sink.val = source.val + S.rowWidth a) :
    FiniteFactorPath D N source sink := by
  have hbound : source.val + S.rowWidth a ≤ N := by
    rw [← hsum]
    exact Nat.le_of_lt_succ sink.isLt
  let f : Fin (finiteFactorStageCount 0 q N + 1) → Fin (N + 1) := fun s ↦
    betaTableauPosition T a source hbound ⟨s.val, by
      simp [finiteFactorStageCount] at s ⊢
      omega⟩
  have hfzero : f 0 = source := by
    dsimp [f]
    convert betaTableauPosition_zero T a source hbound using 1
  have hflast : f (Fin.last (finiteFactorStageCount 0 q N)) = sink := by
    dsimp [f]
    have hlast := betaTableauPosition_last T a source hbound
    convert hlast using 1
    · have hcount : finiteFactorStageCount 0 q N = q := by
        simp [finiteFactorStageCount]
      have heq :
          (⟨finiteFactorStageCount 0 q N,
            by simp [finiteFactorStageCount]⟩ : Fin (q + 1)) = Fin.last q := by
        apply Fin.ext
        simp [finiteFactorStageCount]
      simpa using congrArg (betaTableauPosition T a source hbound) heq
    · apply Fin.ext
      exact hsum
  refine { position := f, source_eq := hfzero, sink_eq := hflast, valid := ?_ }
  intro t
  have ht : t.val < q := by simpa [finiteFactorStageCount] using t.isLt
  let t' : Fin q := ⟨t.val, ht⟩
  have hstep := betaRowMoveCount_step T a t'
  dsimp [f]
  unfold NetworkStepAllowed
  rw [if_pos ht]
  rcases hstep with hstay | hmove
  · left
    have hstep' : betaRowMoveCount T a ⟨t.val + 1, by omega⟩ =
        betaRowMoveCount T a ⟨t.val, by omega⟩ := by
      simpa [t'] using hstay
    dsimp [betaTableauPosition]
    omega
  · right
    have hstep' : betaRowMoveCount T a ⟨t.val + 1, by omega⟩ =
        betaRowMoveCount T a ⟨t.val, by omega⟩ + 1 := by
      simpa [t'] using hmove
    dsimp [betaTableauPosition]
    omega

/-! The first tuple specialization: when `p = 0`, the alpha shape is empty, so every coproduct
tableau row has exactly the displacement required by the reflected network endpoints. -/

theorem rowWidth_eq_zero_of_fitsColumnBound_zero
    {r w : ℕ} {S : FiniteSkewShape r w}
    (hfit : S.FitsColumnBound 0) (a : Fin r) : S.rowWidth a = 0 := by
  by_contra hne
  have hpos : S.inner a < S.outer a := by
    rw [FiniteSkewShape.rowWidth_eq_sub] at hne
    omega
  let c : Fin w := ⟨S.inner a, by
    exact hpos.trans_le (S.outer.rowLength_le_width a)⟩
  have hcell : a ∈ S.columnCells c := by
    rw [FiniteSkewShape.mem_columnCells]
    exact ⟨le_rfl, hpos⟩
  have hcard : 0 < S.columnHeight c := by
    unfold FiniteSkewShape.columnHeight
    exact Finset.card_pos.mpr ⟨a, hcell⟩
  have hc := hfit c
  omega

theorem coproduct_p_zero_intermediate_eq_inner
    {q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) :
    T.intermediate.middle = containedInnerPartition I J hstruct := by
  apply RectanglePartition.rowLength_injective
  funext a
  have hfit := T.tableaux.alphaTableau.fitsColumnBound
  have hrow := rowWidth_eq_zero_of_fitsColumnBound_zero hfit a
  rw [FiniteSkewShape.rowWidth_eq_sub] at hrow
  apply Fin.ext
  change T.intermediate.middle a = containedInnerPartition I J hstruct a
  change T.intermediate.middle a = T.intermediate.alphaShape.inner a
  change T.intermediate.middle a - T.intermediate.alphaShape.inner a = 0 at hrow
  have hle := T.intermediate.inner_le a
  change T.intermediate.alphaShape.inner a ≤ T.intermediate.middle a at hle
  omega

theorem coproduct_p_zero_beta_row_displacement
    {q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) (a : Fin r) :
    (tupleNetworkSink I J hstruct a).val =
      (tupleNetworkSource J a).val + T.intermediate.betaShape.rowWidth a := by
  have hmid := coproduct_p_zero_intermediate_eq_inner T
  rw [FiniteSkewShape.rowWidth_eq_sub]
  change J.tupleWidth - (I a.rev - 1) =
    (J.tupleWidth - (J a.rev - 1)) +
      (containingOuterPartition J a - T.intermediate.middle a)
  rw [hmid]
  change J.tupleWidth - (I a.rev - 1) =
    (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - I.associatedPart a)
  have hassocI : I.associatedPart a = I a.rev - (a.rev.val + 1) := rfl
  have hassocJ : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
  rw [hassocI, hassocJ]
  have hIJ := hstruct a.rev
  have hI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  have hJ := J.value_le_tupleWidth a.rev
  have hIp := I.position_le a.rev
  have hJp := J.position_le a.rev
  omega

noncomputable def coproduct_p_zero_beta_path
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) (a : Fin r) :
    FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
      (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) := by
  apply betaTableauPath (reverseFiniteEdreiData D) T.tableaux.betaTableau a
  exact coproduct_p_zero_beta_row_displacement T a

theorem betaRowStage_lt_iff {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r)
    (c d : BetaRowCell T a) :
    (betaRowStage T a d).val < (betaRowStage T a c).val ↔ c.val < d.val := by
  constructor
  · intro hstage
    have hstageFin : betaRowStage T a d < betaRowStage T a c :=
      Fin.mk_lt_mk.mpr hstage
    have hentry : T.entry ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩ <
      T.entry ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩ := by
      exact Fin.rev_lt_rev.mp (by simpa [betaRowStage] using hstageFin)
    rcases lt_trichotomy c.val d.val with hlt | heq | hgt
    · exact hlt
    · have hcd : c = d := by
        apply Subtype.ext
        exact heq
      subst d
      exact False.elim ((lt_irrefl _) hentry)
    · have hrev := T.row_strict
        (x := ⟨(a, d.val), by
          simpa [FiniteSkewShape.rowCells] using d.property⟩)
        (y := ⟨(a, c.val), by
          simpa [FiniteSkewShape.rowCells] using c.property⟩) rfl hgt
      exact False.elim ((not_lt_of_ge hrev.le) hentry)
  · intro hcol
    have hentry := T.row_strict
      (x := ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩)
      (y := ⟨(a, d.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩) rfl hcol
    exact Fin.rev_lt_rev.mpr hentry

theorem betaRowMoveCount_at_stage_of_cell
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (c : BetaRowCell T a) :
    betaRowMoveCount T a ⟨(betaRowStage T a c).val, by omega⟩ =
      (Finset.univ.filter fun d : BetaRowCell T a => c.val < d.val).card := by
  unfold betaRowMoveCount
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact betaRowStage_lt_iff T a c d

theorem betaRowSuffix_card
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (c : BetaRowCell T a) :
    (Finset.univ.filter fun d : BetaRowCell T a => c.val < d.val).card =
      S.outer a - (c.val.val + 1) := by
  let R : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => c.val < d.val
  let emb : BetaRowCell T a ↪ ℕ :=
    ⟨fun d => d.val.val, by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      exact hxy⟩
  have hmap : R.map emb = Finset.Ico (c.val.val + 1) (S.outer a) := by
    ext j
    constructor
    · intro hj
      obtain ⟨d, hd, hdj⟩ := Finset.mem_map.mp hj
      have hd' := Finset.mem_filter.mp hd
      have hdj' : d.val.val = j := by simpa [emb] using hdj
      subst j
      exact Finset.mem_Ico.mpr ⟨by omega, (FiniteSkewShape.mem_rowCells.mp d.property).2⟩
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      have hjN : j < N := lt_of_lt_of_le hj'.2 (S.outer.rowLength_le_width a)
      let k : Fin N := ⟨j, hjN⟩
      have hkval : k.val = j := rfl
      have hkcell : k ∈ S.rowCells a := by
        apply FiniteSkewShape.mem_rowCells.mpr
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        change S.inner a ≤ k.val ∧ k.val < S.outer a
        omega
      let d : BetaRowCell T a := ⟨k, hkcell⟩
      apply Finset.mem_map.mpr
      refine ⟨d, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change c.val.val < k.val
        omega
      · rfl
  rw [← Finset.card_map, hmap, Nat.card_Ico]

theorem betaRowMoveCount_le_suffix_of_not_counted
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (s : Fin (q + 1))
    (c : BetaRowCell T a)
    (hnot : ¬(betaRowStage T a c).val < s.val) :
    betaRowMoveCount T a s ≤
      (Finset.univ.filter fun d : BetaRowCell T a => c.val < d.val).card := by
  let U : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => (betaRowStage T a d).val < s.val
  let V : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => c.val < d.val
  have hsub : U ⊆ V := by
    intro d hd
    have hdU := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hdc
    have hle : d.val ≤ c.val := Nat.le_of_not_gt hdc
    by_cases heq : d.val = c.val
    · have hdc' : d = c := by
        apply Subtype.ext
        exact heq
      subst d
      exact hnot hdU.2
    · have hlt : d.val < c.val := lt_of_le_of_ne hle heq
      have hstage : (betaRowStage T a c).val <
          (betaRowStage T a d).val := by
        exact (betaRowStage_lt_iff T a d c).mpr hlt
      omega
  have hcard := Finset.card_le_card hsub
  exact hcard

theorem betaRowMoveCount_ge_suffix_at_of_counted
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (s : Fin (q + 1))
    (c : BetaRowCell T a)
    (hcount : (betaRowStage T a c).val < s.val) :
    (Finset.univ.filter fun d : BetaRowCell T a => c.val ≤ d.val).card ≤
      betaRowMoveCount T a s := by
  let U : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => (betaRowStage T a d).val < s.val
  let V : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => c.val ≤ d.val
  have hsub : V ⊆ U := by
    intro d hd
    have hdV := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases heq : d.val = c.val
    · have hdc : d = c := by
        apply Subtype.ext
        exact heq
      subst d
      exact hcount
    · have hlt : c.val < d.val := lt_of_le_of_ne hdV.2 (Ne.symm heq)
      have hstage : (betaRowStage T a d).val <
          (betaRowStage T a c).val :=
        (betaRowStage_lt_iff T a c d).mpr hlt
      omega
  exact Finset.card_le_card hsub

theorem betaRowSuffix_card_inclusive
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (c : BetaRowCell T a) :
    (Finset.univ.filter fun d : BetaRowCell T a => c.val ≤ d.val).card =
      S.outer a - c.val.val := by
  let R : Finset (BetaRowCell T a) :=
    Finset.univ.filter fun d => c.val ≤ d.val
  let emb : BetaRowCell T a ↪ ℕ :=
    ⟨fun d => d.val.val, by
      intro x y hxy
      apply Subtype.ext
      apply Fin.ext
      exact hxy⟩
  have hmap : R.map emb = Finset.Ico c.val.val (S.outer a) := by
    ext j
    constructor
    · intro hj
      obtain ⟨d, hd, hdj⟩ := Finset.mem_map.mp hj
      have hd' := Finset.mem_filter.mp hd
      have hdj' : d.val.val = j := by simpa [emb] using hdj
      subst j
      exact Finset.mem_Ico.mpr ⟨hd'.2, (FiniteSkewShape.mem_rowCells.mp d.property).2⟩
    · intro hj
      have hj' := Finset.mem_Ico.mp hj
      have hjN : j < N := lt_of_lt_of_le hj'.2 (S.outer.rowLength_le_width a)
      let k : Fin N := ⟨j, hjN⟩
      have hkcell : k ∈ S.rowCells a := by
        apply FiniteSkewShape.mem_rowCells.mpr
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        have hclow := hc.1
        have hjlow := hj'.1
        change S.inner a ≤ j ∧ j < S.outer a
        omega
      let d : BetaRowCell T a := ⟨k, hkcell⟩
      apply Finset.mem_map.mpr
      refine ⟨d, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hj'.1⟩
      · rfl
  rw [← Finset.card_map, hmap, Nat.card_Ico]

theorem betaRowMoveCount_lt_iff_boundary_le
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (s : Fin (q + 1))
    (c : BetaRowCell T a) :
    (betaRowStage T a c).val < s.val ↔
      S.outer a - betaRowMoveCount T a s ≤ c.val.val := by
  constructor
  · intro hcount
    have hle := betaRowMoveCount_ge_suffix_at_of_counted T a s c hcount
    rw [betaRowSuffix_card_inclusive] at hle
    have hcnt := betaRowMoveCount_le_width T a s
    have hwidth : S.rowWidth a ≤ S.outer a := by
      rw [FiniteSkewShape.rowWidth_eq_sub]
      omega
    have hc := FiniteSkewShape.mem_rowCells.mp c.property
    have hcout := hc.2
    rw [FiniteSkewShape.rowWidth_eq_sub] at hwidth
    omega
  · intro hboundary
    by_contra hnot
    have hle := betaRowMoveCount_le_suffix_of_not_counted T a s c hnot
    rw [betaRowSuffix_card] at hle
    have hcnt := betaRowMoveCount_le_width T a s
    have hwidth : S.rowWidth a ≤ S.outer a := by
      rw [FiniteSkewShape.rowWidth_eq_sub]
      omega
    have hc := FiniteSkewShape.mem_rowCells.mp c.property
    have hcout := hc.2
    rw [FiniteSkewShape.rowWidth_eq_sub] at hwidth
    omega

theorem betaRowMoveCount_succ_at_stage_of_cell
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (T : BetaSkewTableau S q) (a : Fin r) (c : BetaRowCell T a) :
    betaRowMoveCount T a (⟨(betaRowStage T a c).val + 1, by omega⟩ : Fin (q + 1)) =
        (Finset.univ.filter fun d : BetaRowCell T a => c.val ≤ d.val).card := by
  unfold betaRowMoveCount
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hstage
    rcases lt_trichotomy c.val d.val with hlt | heq | hgt
    · exact le_of_lt hlt
    · exact le_of_eq heq
    · have hstage' : (betaRowStage T a c).val <
          (betaRowStage T a d).val :=
        (betaRowStage_lt_iff T a d c).mpr hgt
      omega
  · intro hcol
    rcases hcol.eq_or_lt with heq | hlt
    · have hcd : c = d := by
        apply Subtype.ext
        exact heq
      subst d
      omega
    · have hstage' : (betaRowStage T a d).val <
          (betaRowStage T a c).val :=
        (betaRowStage_lt_iff T a c d).mpr hlt
      omega

@[simp] theorem betaTableauPath_position
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData 0 q) (T : BetaSkewTableau S q) (a : Fin r)
    {source sink : Fin (N + 1)} (hsum : sink.val = source.val + S.rowWidth a)
    (s : Fin (finiteFactorStageCount 0 q N + 1)) :
    (betaTableauPath D T a hsum).position s =
      betaTableauPosition T a source
        (by
          rw [← hsum]
          exact Nat.le_of_lt_succ sink.isLt)
        ⟨s.val, by
          simp [finiteFactorStageCount] at s ⊢
          omega⟩ := by
  rfl

theorem betaTableauPath_position_before_cell
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData 0 q) (T : BetaSkewTableau S q) (a : Fin r)
    {source sink : Fin (N + 1)} (hsum : sink.val = source.val + S.rowWidth a)
    (c : BetaRowCell T a) :
    (betaTableauPath D T a hsum).position
        (⟨(betaRowStage T a c).val, by
          simp [finiteFactorStageCount]⟩ : Fin (finiteFactorStageCount 0 q N)).castSucc =
      ⟨source.val + S.outer a - (c.val.val + 1), by
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        have hbound : source.val + S.rowWidth a ≤ N := by
          rw [← hsum]
          exact Nat.le_of_lt_succ sink.isLt
        rw [FiniteSkewShape.rowWidth_eq_sub] at hbound
        omega⟩ := by
  rw [betaTableauPath_position]
  apply Fin.ext
  change source.val + betaRowMoveCount T a
      ⟨(betaRowStage T a c).val, by omega⟩ =
    source.val + S.outer a - (c.val.val + 1)
  rw [betaRowMoveCount_at_stage_of_cell, betaRowSuffix_card]
  have hc := FiniteSkewShape.mem_rowCells.mp c.property
  symm
  exact Nat.add_sub_assoc (by omega) source

theorem betaTableauPath_position_after_cell
    {r N q : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData 0 q) (T : BetaSkewTableau S q) (a : Fin r)
    {source sink : Fin (N + 1)} (hsum : sink.val = source.val + S.rowWidth a)
    (c : BetaRowCell T a) :
    (betaTableauPath D T a hsum).position
        (⟨(betaRowStage T a c).val, by
          simp [finiteFactorStageCount]⟩ : Fin (finiteFactorStageCount 0 q N)).succ =
      ⟨source.val + S.outer a - c.val.val, by
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        have hbound : source.val + S.rowWidth a ≤ N := by
          rw [← hsum]
          exact Nat.le_of_lt_succ sink.isLt
        rw [FiniteSkewShape.rowWidth_eq_sub] at hbound
        omega⟩ := by
  rw [betaTableauPath_position]
  apply Fin.ext
  change source.val + betaRowMoveCount T a
      (⟨(betaRowStage T a c).val + 1, by omega⟩ : Fin (q + 1)) =
    source.val + S.outer a - c.val.val
  rw [betaRowMoveCount_succ_at_stage_of_cell, betaRowSuffix_card_inclusive]
  have hc := FiniteSkewShape.mem_rowCells.mp c.property
  symm
  exact Nat.add_sub_assoc (by omega) source

noncomputable def coproduct_p_zero_term
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) :
    TupleFiniteFactorNetworkTerm D I J hstruct :=
  ⟨Equiv.refl (Fin r), fun a ↦ coproduct_p_zero_beta_path D T a⟩

theorem coproduct_p_zero_term_path_position_before_cell
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct)
    (a : Fin r) (c : BetaRowCell T.tableaux.betaTableau a) :
    ((coproduct_p_zero_term D T).2 a).position
        (⟨(betaRowStage T.tableaux.betaTableau a c).val, by
          simp [finiteFactorStageCount]⟩ :
          Fin (finiteFactorStageCount 0 q J.tupleWidth)).castSucc =
      ⟨(J.tupleWidth - (a.rev.val + c.val.val + 1)), by
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        have hcouter := hc.2
        change c.val.val < J a.rev - (a.rev.val + 1) at hcouter
        have hJ := J.value_le_tupleWidth a.rev
        have hpos := J.position_le a.rev
        change J.tupleWidth - (a.rev.val + c.val.val + 1) < J.tupleWidth + 1
        omega⟩ := by
  let hsum := coproduct_p_zero_beta_row_displacement T a
  have hpos := betaTableauPath_position_before_cell
    (reverseFiniteEdreiData D) T.tableaux.betaTableau a hsum c
  change (betaTableauPath (reverseFiniteEdreiData D)
      T.tableaux.betaTableau a hsum).position _ = _
  rw [hpos]
  apply Fin.ext
  change (tupleNetworkSource J a).val +
      T.intermediate.betaShape.outer a - (c.val.val + 1) =
    J.tupleWidth - (a.rev.val + c.val.val + 1)
  change (J.tupleWidth - (J a.rev - 1)) +
      containingOuterPartition J a - (c.val.val + 1) =
    J.tupleWidth - (a.rev.val + c.val.val + 1)
  have houter : containingOuterPartition J a =
      J a.rev - (a.rev.val + 1) := rfl
  rw [houter]
  have hJ := J.value_le_tupleWidth a.rev
  have hposA := J.position_le a.rev
  omega

theorem coproduct_p_zero_term_good
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) :
    NetworkTermGood (coproduct_p_zero_term D T) := by
  intro a b hab s
  let TB := T.tableaux.betaTableau
  let sa : Fin (q + 1) := ⟨s.val, by simpa [finiteFactorStageCount] using s.isLt⟩
  let N := J.tupleWidth
  have hsumA := coproduct_p_zero_beta_row_displacement T a
  have hsumB := coproduct_p_zero_beta_row_displacement T b
  have hposA : (((coproduct_p_zero_term D T).2 a).position s).val =
      N - (a.rev.val +
        (T.intermediate.betaShape.outer a - betaRowMoveCount TB a sa)) := by
    have h := betaTableauPath_position (reverseFiniteEdreiData D) TB a hsumA s
    have h' := congrArg Fin.val h
    change (((coproduct_p_zero_term D T).2 a).position s).val = _ at h'
    change N - (J a.rev - 1) + betaRowMoveCount TB a sa = _ at h'
    change N - (J a.rev - 1) + betaRowMoveCount TB a sa =
      N - (a.rev.val + (T.intermediate.betaShape.outer a -
        betaRowMoveCount TB a sa))
    have houter : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    rw [houter]
    have hcount := betaRowMoveCount_le_width TB a sa
    have hrow := T.intermediate.betaShape.rowWidth_eq_sub a
    have houter := T.intermediate.betaShape.outer.rowLength_le_width a
    rw [T.intermediate.betaShape.rowWidth_eq_sub] at hcount
    have hinner := T.intermediate.betaShape.inner_le_outer a
    change T.intermediate.betaShape.inner a ≤ T.intermediate.betaShape.outer a at hinner
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hposB : (((coproduct_p_zero_term D T).2 b).position s).val =
      N - (b.rev.val +
        (T.intermediate.betaShape.outer b - betaRowMoveCount TB b sa)) := by
    have h := betaTableauPath_position (reverseFiniteEdreiData D) TB b hsumB s
    have h' := congrArg Fin.val h
    change (((coproduct_p_zero_term D T).2 b).position s).val = _ at h'
    change N - (J b.rev - 1) + betaRowMoveCount TB b sa = _ at h'
    change N - (J b.rev - 1) + betaRowMoveCount TB b sa =
      N - (b.rev.val + (T.intermediate.betaShape.outer b -
        betaRowMoveCount TB b sa))
    have houter : T.intermediate.betaShape.outer b =
        J b.rev - (b.rev.val + 1) := rfl
    rw [houter]
    have hcount := betaRowMoveCount_le_width TB b sa
    have hrow := T.intermediate.betaShape.rowWidth_eq_sub b
    have houter := T.intermediate.betaShape.outer.rowLength_le_width b
    rw [T.intermediate.betaShape.rowWidth_eq_sub] at hcount
    have hinner := T.intermediate.betaShape.inner_le_outer b
    change T.intermediate.betaShape.inner b ≤ T.intermediate.betaShape.outer b at hinner
    have hJ := J.value_le_tupleWidth b.rev
    have hpos := J.position_le b.rev
    omega
  by_contra hcoll
  have hcollVal := congrArg Fin.val hcoll
  rw [hposA, hposB] at hcollVal
  have hrev : b.rev.val < a.rev.val := by
    have := Fin.rev_lt_rev.mpr hab
    exact Fin.mk_lt_mk.mp this
  let xa := T.intermediate.betaShape.outer a - betaRowMoveCount TB a sa
  let xb := T.intermediate.betaShape.outer b - betaRowMoveCount TB b sa
  have hxaN : a.rev.val + xa ≤ N := by
    dsimp [xa, N]
    have houter := T.intermediate.betaShape.outer.rowLength_le_width a
    have hrev := a.rev.isLt
    have houterEq : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    have hxa_le : T.intermediate.betaShape.outer a -
        betaRowMoveCount TB a sa ≤ T.intermediate.betaShape.outer a :=
      Nat.sub_le _ _
    change a.rev.val + (T.intermediate.betaShape.outer a -
      betaRowMoveCount TB a sa) ≤ N
    rw [houterEq]
    omega
  have hxbN : b.rev.val + xb ≤ N := by
    dsimp [xb, N]
    have houter := T.intermediate.betaShape.outer.rowLength_le_width b
    have hrev := b.rev.isLt
    have houterEq : T.intermediate.betaShape.outer b =
        J b.rev - (b.rev.val + 1) := rfl
    have hJ := J.value_le_tupleWidth b.rev
    have hpos := J.position_le b.rev
    have hxb_le : T.intermediate.betaShape.outer b -
        betaRowMoveCount TB b sa ≤ T.intermediate.betaShape.outer b :=
      Nat.sub_le _ _
    change b.rev.val + (T.intermediate.betaShape.outer b -
      betaRowMoveCount TB b sa) ≤ N
    rw [houterEq]
    omega
  have hxeq : a.rev.val + xa = b.rev.val + xb := by
    have hEqSub : N - (a.rev.val + xa) = N - (b.rev.val + xb) := by
      simpa [xa, xb] using hcollVal
    have hcancelA := Nat.sub_add_cancel hxaN
    have hcancelB := Nat.sub_add_cancel hxbN
    have hsum : N - (a.rev.val + xa) + (a.rev.val + xa) =
        N - (b.rev.val + xb) + (b.rev.val + xb) :=
      hcancelA.trans hcancelB.symm
    rw [hEqSub] at hsum
    exact Nat.add_left_cancel hsum
  have hxbgt : xa < xb := by omega
  have hxain : T.intermediate.betaShape.inner a ≤ xa := by
    dsimp [xa]
    have hcount := betaRowMoveCount_le_width TB a sa
    rw [T.intermediate.betaShape.rowWidth_eq_sub] at hcount
    have hinner := T.intermediate.betaShape.inner_le_outer a
    change T.intermediate.betaShape.inner a ≤ T.intermediate.betaShape.outer a at hinner
    have hcancel := Nat.sub_add_cancel hinner
    have hcount_outer := hcount.trans (Nat.sub_le _ _)
    have hcancel_count := Nat.sub_add_cancel hcount_outer
    have hadd : T.intermediate.betaShape.inner a +
        betaRowMoveCount TB a sa ≤ T.intermediate.betaShape.outer a := by
      calc
        T.intermediate.betaShape.inner a + betaRowMoveCount TB a sa ≤
            T.intermediate.betaShape.inner a +
              (T.intermediate.betaShape.outer a - T.intermediate.betaShape.inner a) :=
          Nat.add_le_add_left hcount _
        _ = T.intermediate.betaShape.outer a := by omega
    exact Nat.le_sub_of_add_le hadd
  have hxbin : T.intermediate.betaShape.inner b ≤ xa := by
    have hinner := T.intermediate.betaShape.inner.antitone hab.le
    change T.intermediate.betaShape.inner b ≤ T.intermediate.betaShape.inner a at hinner
    exact hinner.trans hxain
  have hxaout : xa < T.intermediate.betaShape.outer a := by
    have hxbout : xb ≤ T.intermediate.betaShape.outer b := by
      dsimp [xb]
      exact Nat.sub_le _ _
    have hout := T.intermediate.betaShape.outer.antitone hab.le
    change T.intermediate.betaShape.outer b ≤ T.intermediate.betaShape.outer a at hout
    omega
  have hxbout : xb ≤ T.intermediate.betaShape.outer b := by
    dsimp [xb]
    exact Nat.sub_le _ _
  have hxaoutB : xa < T.intermediate.betaShape.outer b :=
    hxbgt.trans_le hxbout
  let cA : BetaRowCell TB a := ⟨⟨xa, by
      have houter := T.intermediate.betaShape.outer.rowLength_le_width a
      omega⟩, by
        apply FiniteSkewShape.mem_rowCells.mpr
        exact ⟨hxain, hxaout⟩⟩
  let cB : BetaRowCell TB b := ⟨⟨xa, by
      have houter := T.intermediate.betaShape.outer.rowLength_le_width a
      have hout := T.intermediate.betaShape.outer.rowLength_le_width b
      omega⟩, by
        apply FiniteSkewShape.mem_rowCells.mpr
        exact ⟨hxbin, hxaoutB⟩⟩
  have hcountA : (betaRowStage TB a cA).val < sa.val := by
    apply (betaRowMoveCount_lt_iff_boundary_le TB a sa cA).mpr
    dsimp [cA, xa]
    rfl
  have hnotB : ¬(betaRowStage TB b cB).val < sa.val := by
    intro hcountB
    have hbd := (betaRowMoveCount_lt_iff_boundary_le TB b sa cB).mp hcountB
    have hbd' : xb ≤ xa := by
      simpa [cB, xb] using hbd
    omega
  have hcol := TB.column_weak (x := ⟨(a, cA.val), by
      simpa [FiniteSkewShape.rowCells] using cA.property⟩)
      (y := ⟨(b, cB.val), by
        simpa [FiniteSkewShape.rowCells] using cB.property⟩) rfl hab.le
  have hstage_order : (betaRowStage TB b cB).val ≤
      (betaRowStage TB a cA).val := by
    exact Fin.rev_le_rev.mpr (Fin.mk_le_mk.mpr hcol)
  omega

end

end ToeplitzPositroids.Edrei
