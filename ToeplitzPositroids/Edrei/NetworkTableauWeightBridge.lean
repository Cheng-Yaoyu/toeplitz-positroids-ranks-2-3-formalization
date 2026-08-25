import ToeplitzPositroids.Edrei.NetworkTableauBridge

/-!
# Move-stage/cell correspondences for the network/tableau bridge

This file supplies the inverse direction of the crossing-stage encoding.  It starts with the
beta stages, where one chip is visited at each time and a move stage is exactly one beta cell.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

def BetaMovePredicate
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (t : Fin q) : Prop :=
  (F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).succ ≠
    (F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).castSucc

abbrev BetaMoveIndex
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :=
  Σ a : Fin r, {t : Fin q // BetaMovePredicate F a t}

theorem beta_move_stage_is_unit_move
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (t : Fin q) (hmove : BetaMovePredicate F a t) :
    ((F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).succ).val =
      ((F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val + 1 := by
  have hvalid := (F.1.2 a).valid (betaStage (p := p) (N := J.tupleWidth) t)
  have htq : (betaStage (p := p) (N := J.tupleWidth) t).val < q := by
    change t.val < q
    exact t.isLt
  unfold NetworkStepAllowed at hvalid
  rw [if_pos htq] at hvalid
  rcases hvalid with hstay | hstep
  · exact False.elim (hmove (Fin.ext hstay))
  · exact hstep

theorem beta_move_stage_bounds
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (t : Fin q) (hmove : BetaMovePredicate F a t) :
    a.rev.val +
        ((F.1.2 a).position
          (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val + 1 ≤
      J.tupleWidth ∧
      F.intermediate.middle a ≤
        J.tupleWidth - (a.rev.val +
          ((F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val + 1) ∧
      J.tupleWidth - (a.rev.val +
          ((F.1.2 a).position (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val + 1) <
        containingOuterPartition J a := by
  let P := F.1.2 a
  let N := J.tupleWidth
  let s := betaStage (p := p) (N := J.tupleWidth) t
  let k := (P.position s.castSucc).val
  have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
  have ha : F.1.1 a = a := by rw [hperm]; rfl
  have hmove' := beta_move_stage_is_unit_move F a t hmove
  have hboundaryVertex : s.succ ≤ betaBoundaryVertex p q N := by
    change t.val + 1 ≤ q
    omega
  have hboundary := P.position_monotone hboundaryVertex
  change (P.position s.succ).val ≤ (P.position (betaBoundaryVertex p q N)).val at hboundary
  have hsink := P.position_le_sink (betaBoundaryVertex p q N)
  change (P.position (betaBoundaryVertex p q N)).val ≤
    (tupleNetworkSink I J hstruct a).val at hsink
  have hsource := P.source_le_position s.castSucc
  change (tupleNetworkSource J (F.1.1 a)).val ≤ (P.position s.castSucc).val at hsource
  have hsourceA : (tupleNetworkSource J a).val ≤ (P.position s.castSucc).val := by
    simpa [ha] using hsource
  have hsourceBound : a.rev.val + (tupleNetworkSource J a).val ≤ N := by
    change a.rev.val + (N - (J a.rev - 1)) ≤ N
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hsinkBound : a.rev.val + (tupleNetworkSink I J hstruct a).val ≤ N := by
    change a.rev.val + (N - (I a.rev - 1)) ≤ N
    have hI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
    have hpos := I.position_le a.rev
    omega
  have hsumK : a.rev.val + k + 1 ≤ N := by
    dsimp only [k]
    have hstepBound : (P.position s.succ).val ≤
        (P.position (betaBoundaryVertex p q N)).val := hboundary
    have hstepSink : (P.position s.succ).val ≤
        (tupleNetworkSink I J hstruct a).val := hstepBound.trans hsink
    have hstep : (P.position s.succ).val =
        (P.position s.castSucc).val + 1 := by
      simpa [P, s] using hmove'
    rw [hstep] at hstepSink
    omega
  have hsumSource : a.rev.val + (tupleNetworkSource J a).val <
      a.rev.val + k + 1 := by
    have hk := hsourceA
    dsimp only [k] at hk ⊢
    omega
  have hmiddleEq : F.intermediate.middle a =
      N - (a.rev.val + (P.position (betaBoundaryVertex p q N)).val) := by
    rfl
  have houterEq : containingOuterPartition J a =
      N - (a.rev.val + (tupleNetworkSource J a).val) := by
    symm
    exact reflectedWirePart_source J a
  constructor
  · exact hsumK
  constructor
  · rw [hmiddleEq]
    have hstep : (P.position s.succ).val =
        (P.position s.castSucc).val + 1 := by
      simpa [P, s] using hmove'
    have harg : a.rev.val + k + 1 ≤
        a.rev.val + (P.position (betaBoundaryVertex p q N)).val := by
      dsimp only [k]
      rw [hstep] at hboundary
      omega
    exact Nat.sub_le_sub_left harg N
  · rw [houterEq]
    apply Nat.sub_lt_sub_left
    · omega
    · exact hsumSource

def betaMoveCell
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : BetaMoveIndex F) : (F.intermediate.betaShape).Cell := by
  let a := z.1
  let t := z.2.1
  let k := ((F.1.2 a).position
      (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val
  have hb := beta_move_stage_bounds F a t z.2.2
  let c : Fin J.tupleWidth :=
    ⟨J.tupleWidth - (a.rev.val + k + 1), by omega⟩
  refine ⟨(a, c), ?_⟩
  apply FiniteSkewShape.mem_cells.mpr
  change F.intermediate.middle a ≤ c.val ∧ c.val < containingOuterPartition J a
  exact ⟨by simpa [c] using hb.2.1, by simpa [c] using hb.2.2⟩

theorem betaMoveCell_wire
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : BetaMoveIndex F) :
    (betaCellCrossingWire F (betaMoveCell F z)).val =
      ((F.1.2 z.1).position
        (betaStage (p := p) (N := J.tupleWidth) z.2.1).castSucc).val := by
  let a := z.1
  let t := z.2.1
  let k := ((F.1.2 a).position
      (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val
  have hsum := (beta_move_stage_bounds F a t z.2.2).1
  change J.tupleWidth - (a.rev.val +
      (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
  omega

theorem betaMoveCell_crossingStage
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : BetaMoveIndex F) :
    betaCellCrossingStage F (betaMoveCell F z) =
      betaStage (p := p) (N := J.tupleWidth) z.2.1 := by
  unfold betaCellCrossingStage
  symm
  apply (F.1.2 z.1).crossingStage_unique
    (betaCellCrossingWire F (betaMoveCell F z)).val
    (betaCell_crossing_bounds F (betaMoveCell F z)).1
    (betaCell_crossing_bounds F (betaMoveCell F z)).2.1
  have hwire := betaMoveCell_wire F z
  have hmove := beta_move_stage_is_unit_move F z.1 z.2.1 z.2.2
  constructor
  · rw [hwire]
  · rw [hwire]
    exact hmove

theorem betaMoveCell_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
  (z : BetaMoveIndex F) :
    betaCellEntry F (betaMoveCell F z) = z.2.1.rev := by
  unfold betaCellEntry
  have hstage := betaMoveCell_crossingStage F z
  have hfin :
      (⟨(betaCellCrossingStage F (betaMoveCell F z)).val,
        betaCellCrossingStage_lt_q F (betaMoveCell F z)⟩ : Fin q) = z.2.1 := by
    apply Fin.ext
    simpa using congrArg Fin.val hstage
  simp [hfin]

def betaCellToMoveIndex
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) : BetaMoveIndex F := by
  let t : Fin q :=
    ⟨(betaCellCrossingStage F x).val, betaCellCrossingStage_lt_q F x⟩
  have ht : betaStage (p := p) (N := J.tupleWidth) t =
      betaCellCrossingStage F x := by
    apply Fin.ext
    rfl
  refine ⟨x.val.1, ⟨t, ?_⟩⟩
  intro hstay
  have hspec := betaCellCrossingStage_spec F x
  have hcur :
      ((F.1.2 x.val.1).position
        (betaStage (p := p) (N := J.tupleWidth) t).succ).val =
        (betaCellCrossingWire F x).val + 1 := by
    simpa [ht] using hspec.2
  have hcur' :
      ((F.1.2 x.val.1).position
        (betaStage (p := p) (N := J.tupleWidth) t).castSucc).val =
        (betaCellCrossingWire F x).val := by
    simpa [ht] using hspec.1
  have hval := congrArg Fin.val hstay
  omega

theorem betaMoveCell_left_inverse
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    betaMoveCell F (betaCellToMoveIndex F x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    let z := betaCellToMoveIndex F x
    have hwire := betaMoveCell_wire F z
    have hspec := betaCellCrossingStage_spec F x
    have ht : betaStage (p := p) (N := J.tupleWidth) z.2.1 =
        betaCellCrossingStage F x := by
      apply Fin.ext
      rfl
    have hbefore :
        ((F.1.2 x.val.1).position
          (betaStage (p := p) (N := J.tupleWidth) z.2.1).castSucc).val =
        (betaCellCrossingWire F x).val := by
      simpa [ht] using hspec.1
    have hbefore' :
        ((F.1.2 (betaCellToMoveIndex F x).1).position
          (betaStage (p := p) (N := J.tupleWidth)
            (betaCellToMoveIndex F x).2.1).castSucc).val =
        (betaCellCrossingWire F x).val := by
      simpa [betaCellToMoveIndex] using hbefore
    change (betaMoveCell F z).val.2.val = x.val.2.val
    have hrow : z.1 = x.val.1 := by
      rfl
    change J.tupleWidth -
      ((betaCellToMoveIndex F x).1.rev.val +
        ((F.1.2 (betaCellToMoveIndex F x).1).position
          (betaStage (p := p) (N := J.tupleWidth)
            (betaCellToMoveIndex F x).2.1).castSucc).val + 1) =
      x.val.2.val
    rw [hbefore', betaCellCrossingWire_val]
    have hrowrev : (betaCellToMoveIndex F x).1.rev.val = x.val.1.rev.val := by
      rfl
    rw [hrowrev]
    have hbound := betaCell_wire_bound F x
    omega

theorem betaCellToMoveIndex_right_inverse
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : BetaMoveIndex F) :
    betaCellToMoveIndex F (betaMoveCell F z) = z := by
  rcases z with ⟨a, ⟨t, ht⟩⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    have hstage := betaMoveCell_crossingStage F ⟨a, ⟨t, ht⟩⟩
    change (betaCellCrossingStage F (betaMoveCell F ⟨a, ⟨t, ht⟩⟩)).val = t.val
    have hstageVal := congrArg Fin.val hstage
    simpa using hstageVal

def betaMoveCellEquiv
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    BetaMoveIndex F ≃ (F.intermediate.betaShape).Cell where
  toFun := betaMoveCell F
  invFun := betaCellToMoveIndex F
  left_inv := betaCellToMoveIndex_right_inverse F
  right_inv := betaMoveCell_left_inverse F

theorem betaMoveCellEquiv_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : BetaMoveIndex F) :
    betaCellEntry F (betaMoveCellEquiv F z) = z.2.1.rev :=
  betaMoveCell_entry F z

theorem reversePathBetaProduct_eq_move_product
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) :
    reversePathBetaProduct (F.1.2 a) =
      @Finset.prod {t : Fin q // BetaMovePredicate F a t} ℝ Real.instCommMonoid
        (@Finset.univ _ (@Subtype.fintype (Fin q) (BetaMovePredicate F a)
          (Classical.decPred _) (Fin.fintype q)))
        (fun t => D.beta t.1.rev) := by
  classical
  unfold reversePathBetaProduct
  have hfilter := Finset.prod_filter (s := (Finset.univ : Finset (Fin q)))
    (BetaMovePredicate F a) (fun t : Fin q => D.beta t.rev)
  have hsub := Finset.prod_subtype_eq_prod_filter
    (s := (Finset.univ : Finset (Fin q)))
    (p := BetaMovePredicate F a)
    (f := fun t : Fin q => D.beta t.rev)
  have hpoint : ∀ t : Fin q,
         (if ((F.1.2 a).position (betaStage t).succ).val =
            ((F.1.2 a).position (betaStage t).castSucc).val then 1
         else D.beta t.rev) =
        (if BetaMovePredicate F a t then D.beta t.rev else 1) := by
    intro t
    by_cases hval :
        ((F.1.2 a).position (betaStage t).succ).val =
          ((F.1.2 a).position (betaStage t).castSucc).val
    · have hfin : ¬ BetaMovePredicate F a t := by
        intro hmove
        exact hmove (Fin.ext hval)
      simp [hval, hfin]
    · have hfin : BetaMovePredicate F a t := by
        intro heq
        exact hval (congrArg Fin.val heq)
      simp [hval, hfin]
  have hsub2 :
      (∏ t with BetaMovePredicate F a t, D.beta t.rev) =
        @Finset.prod {t : Fin q // BetaMovePredicate F a t} ℝ Real.instCommMonoid
          (@Finset.univ _ (@Subtype.fintype (Fin q) (BetaMovePredicate F a)
            (Classical.decPred _) (Fin.fintype q)))
          (fun t => D.beta t.1.rev) := by
    exact @Finset.prod_subtype (Fin q) ℝ Real.instCommMonoid
      (BetaMovePredicate F a)
      (@Subtype.fintype (Fin q) (BetaMovePredicate F a)
        (Classical.decPred _) (Fin.fintype q))
      ((Finset.univ : Finset (Fin q)).filter (BetaMovePredicate F a))
      (by intro t; simp)
      (fun t : Fin q => D.beta t.rev)
  calc
    (∏ t : Fin q,
        (if ((F.1.2 a).position (betaStage t).succ).val =
            ((F.1.2 a).position (betaStage t).castSucc).val then 1
         else D.beta t.rev)) =
        (∏ t : Fin q, (if BetaMovePredicate F a t then D.beta t.rev else 1)) := by
          apply Finset.prod_congr rfl
          intro t ht
          exact hpoint t
    _ = ∏ t with BetaMovePredicate F a t, D.beta t.rev := hfilter.symm
    _ = @Finset.prod {t : Fin q // BetaMovePredicate F a t} ℝ Real.instCommMonoid
          (@Finset.univ _ (@Subtype.fintype (Fin q) (BetaMovePredicate F a)
            (Classical.decPred _) (Fin.fintype q)))
          (fun t => D.beta t.1.rev) := hsub2

theorem tuplePathFamily_beta_product_eq
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    (∏ a : Fin r, reversePathBetaProduct (F.1.2 a)) =
      ∏ x : (F.intermediate.betaShape).Cell,
        D.beta (betaCellEntry F x) := by
  classical
  have hrow : ∀ a : Fin r,
      reversePathBetaProduct (F.1.2 a) =
        ∏ t : {t : Fin q // BetaMovePredicate F a t}, D.beta t.1.rev := by
    intro a
    exact reversePathBetaProduct_eq_move_product F a
  calc
    (∏ a : Fin r, reversePathBetaProduct (F.1.2 a)) =
        ∏ a : Fin r, ∏ t : {t : Fin q // BetaMovePredicate F a t},
          D.beta t.1.rev := by
      apply Finset.prod_congr rfl
      intro a ha
      exact hrow a
    _ = ∏ z : BetaMoveIndex F, D.beta z.2.1.rev := by
      symm
      exact Fintype.prod_sigma (fun z : BetaMoveIndex F => D.beta z.2.1.rev)
    _ = ∏ x : (F.intermediate.betaShape).Cell,
        D.beta (betaCellEntry F x) := by
      apply Fintype.prod_equiv (betaMoveCellEquiv F)
      intro z
      rw [betaMoveCellEquiv_entry]

def AlphaMovePredicate
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (u : Fin (p * J.tupleWidth)) : Prop :=
  (F.1.2 a).position
      (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ ≠
    (F.1.2 a).position
      (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc

abbrev AlphaMoveIndex
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :=
  Σ a : Fin r, {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u}

theorem alpha_move_stage_is_unit_move
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (u : Fin (p * J.tupleWidth))
    (hmove : AlphaMovePredicate F a u) :
    ((F.1.2 a).position
      (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ).val =
      ((F.1.2 a).position
        (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val + 1 := by
  let s := alphaStageOffset (q := q) (N := J.tupleWidth) u
  have hvalid := (F.1.2 a).valid s
  have hnotbeta : ¬s.val < q := by
    change ¬q + u.val < q
    omega
  unfold NetworkStepAllowed at hvalid
  rw [if_neg hnotbeta] at hvalid
  rcases hvalid with hstay | hstep
  · exact False.elim (hmove (Fin.ext hstay))
  · exact hstep.2.2

theorem alpha_move_stage_bounds
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (u : Fin (p * J.tupleWidth))
    (hmove : AlphaMovePredicate F a u) :
    a.rev.val +
        ((F.1.2 a).position
          (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val + 1 ≤
      J.tupleWidth ∧
      containedInnerPartition I J hstruct a ≤
        J.tupleWidth - (a.rev.val +
          ((F.1.2 a).position
            (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val + 1) ∧
      J.tupleWidth - (a.rev.val +
          ((F.1.2 a).position
            (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val + 1) <
        F.intermediate.middle a := by
  let P := F.1.2 a
  let N := J.tupleWidth
  let s := alphaStageOffset (q := q) (N := J.tupleWidth) u
  let k := (P.position s.castSucc).val
  have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
  have ha : F.1.1 a = a := by rw [hperm]; rfl
  have hmove' := alpha_move_stage_is_unit_move F a u hmove
  have hboundaryVertex : betaBoundaryVertex p q N ≤ s.castSucc := by
    change q ≤ q + u.val
    omega
  have hboundary := P.position_monotone hboundaryVertex
  change (P.position (betaBoundaryVertex p q N)).val ≤ (P.position s.castSucc).val at hboundary
  have hsink := P.position_le_sink s.succ
  change (P.position s.succ).val ≤
    (tupleNetworkSink I J hstruct a).val at hsink
  have hsource := P.source_le_position s.castSucc
  change (tupleNetworkSource J (F.1.1 a)).val ≤ (P.position s.castSucc).val at hsource
  have hsourceA : (tupleNetworkSource J a).val ≤ (P.position s.castSucc).val := by
    simpa [ha] using hsource
  have hsourceBound : a.rev.val + (tupleNetworkSource J a).val ≤ N := by
    change a.rev.val + (N - (J a.rev - 1)) ≤ N
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hsinkBound : a.rev.val + (tupleNetworkSink I J hstruct a).val ≤ N := by
    change a.rev.val + (N - (I a.rev - 1)) ≤ N
    have hI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
    have hpos := I.position_le a.rev
    omega
  have hsumK : a.rev.val + k + 1 ≤ N := by
    dsimp only [k]
    have hstepSink : (P.position s.succ).val ≤
        (tupleNetworkSink I J hstruct a).val := hsink
    have hstep : (P.position s.succ).val =
        (P.position s.castSucc).val + 1 := by
      simpa [P, s] using hmove'
    rw [hstep] at hstepSink
    omega
  have hsumBoundary :
      a.rev.val + (P.position (betaBoundaryVertex p q N)).val <
        a.rev.val + k + 1 := by
    dsimp only [k]
    omega
  have hmiddleEq : F.intermediate.middle a =
      N - (a.rev.val + (P.position (betaBoundaryVertex p q N)).val) := by
    rfl
  have hinnerEq : containedInnerPartition I J hstruct a =
      N - (a.rev.val + (tupleNetworkSink I J hstruct a).val) := by
    symm
    exact reflectedWirePart_sink I J hstruct a
  have houterEq : containingOuterPartition J a =
      N - (a.rev.val + (tupleNetworkSource J a).val) := by
    symm
    exact reflectedWirePart_source J a
  constructor
  · exact hsumK
  constructor
  · rw [hinnerEq]
    have harg : a.rev.val + k + 1 ≤
        a.rev.val + (tupleNetworkSink I J hstruct a).val := by
      dsimp only [k]
      rw [show (P.position s.succ).val =
        (P.position s.castSucc).val + 1 by simpa [P, s] using hmove'] at hsink
      omega
    exact Nat.sub_le_sub_left harg N
  · rw [hmiddleEq]
    change N - (a.rev.val + k + 1) <
      N - (a.rev.val + (P.position (betaBoundaryVertex p q N)).val)
    omega

def alphaMoveCell
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) : (F.intermediate.alphaShape).Cell := by
  let a := z.1
  let u := z.2.1
  let k := ((F.1.2 a).position
      (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val
  have hb := alpha_move_stage_bounds F a u z.2.2
  let c : Fin J.tupleWidth :=
    ⟨J.tupleWidth - (a.rev.val + k + 1), by omega⟩
  refine ⟨(a, c), ?_⟩
  apply FiniteSkewShape.mem_cells.mpr
  change containedInnerPartition I J hstruct a ≤ c.val ∧
    c.val < F.intermediate.middle a
  exact ⟨by simpa [c] using hb.2.1, by simpa [c] using hb.2.2⟩

theorem alphaMoveCell_wire
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) :
    (alphaCellCrossingWire F (alphaMoveCell F z)).val =
      ((F.1.2 z.1).position
        (alphaStageOffset (q := q) (N := J.tupleWidth) z.2.1).castSucc).val := by
  let a := z.1
  let u := z.2.1
  let k := ((F.1.2 a).position
      (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val
  have hsum := (alpha_move_stage_bounds F a u z.2.2).1
  change J.tupleWidth - (a.rev.val +
      (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
  omega

theorem alphaMoveCell_crossingStage
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) :
    alphaCellCrossingStage F (alphaMoveCell F z) =
      alphaStageOffset (q := q) (N := J.tupleWidth) z.2.1 := by
  unfold alphaCellCrossingStage
  symm
  apply (F.1.2 z.1).crossingStage_unique
    (alphaCellCrossingWire F (alphaMoveCell F z)).val
    (alphaCell_crossing_bounds F (alphaMoveCell F z)).1
    (alphaCell_crossing_bounds F (alphaMoveCell F z)).2.1
  have hwire := alphaMoveCell_wire F z
  have hmove := alpha_move_stage_is_unit_move F z.1 z.2.1 z.2.2
  constructor
  · rw [hwire]
  · rw [hwire]
    exact hmove

theorem alphaMoveCell_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) :
    alphaCellEntry F (alphaMoveCell F z) =
      (alphaStageIndex (N := J.tupleWidth) z.2.1).rev := by
  unfold alphaCellEntry
  have hstage := alphaMoveCell_crossingStage F z
  have hval :
      ((alphaCellCrossingStage F (alphaMoveCell F z)).val - q) /
          J.tupleWidth = (alphaStageIndex (N := J.tupleWidth) z.2.1).val := by
    rw [hstage]
    change (q + z.2.1.val - q) / J.tupleWidth = z.2.1.val / J.tupleWidth
    rw [Nat.add_sub_cancel_left]
  have hfin :
      (⟨((alphaCellCrossingStage F (alphaMoveCell F z)).val - q) /
          J.tupleWidth,
        alphaCellCrossingStage_alpha_index_bound F (alphaMoveCell F z)⟩ : Fin p) =
        alphaStageIndex (N := J.tupleWidth) z.2.1 := by
    apply Fin.ext
    exact hval
  simp [hfin]

def alphaCellToMoveIndex
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) : AlphaMoveIndex F := by
  let u : Fin (p * J.tupleWidth) :=
    ⟨(alphaCellCrossingStage F x).val - q,
      alphaCellCrossingStage_alpha_index_lt_p F x⟩
  have hstage :
      alphaStageOffset (q := q) (N := J.tupleWidth) u =
        alphaCellCrossingStage F x := by
    apply Fin.ext
    change q + ((alphaCellCrossingStage F x).val - q) =
      (alphaCellCrossingStage F x).val
    have htq := alphaCellCrossingStage_ge_q F x
    omega
  refine ⟨x.val.1, ⟨u, ?_⟩⟩
  intro hstay
  have hspec := alphaCellCrossingStage_spec F x
  have hcur :
      ((F.1.2 x.val.1).position
        (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ).val =
        (alphaCellCrossingWire F x).val + 1 := by
    simpa [hstage] using hspec.2
  have hbefore :
      ((F.1.2 x.val.1).position
        (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val =
        (alphaCellCrossingWire F x).val := by
    simpa [hstage] using hspec.1
  have hval := congrArg Fin.val hstay
  omega

theorem alphaMoveCell_left_inverse
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    alphaMoveCell F (alphaCellToMoveIndex F x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext
    let z := alphaCellToMoveIndex F x
    have hspec := alphaCellCrossingStage_spec F x
    have ht :
        alphaStageOffset (q := q) (N := J.tupleWidth) z.2.1 =
          alphaCellCrossingStage F x := by
      apply Fin.ext
      change q + ((alphaCellCrossingStage F x).val - q) =
        (alphaCellCrossingStage F x).val
      have htq := alphaCellCrossingStage_ge_q F x
      omega
    have hbefore :
        ((F.1.2 x.val.1).position
          (alphaStageOffset (q := q) (N := J.tupleWidth) z.2.1).castSucc).val =
        (alphaCellCrossingWire F x).val := by
      simpa [ht] using hspec.1
    have hbefore' :
        ((F.1.2 (alphaCellToMoveIndex F x).1).position
          (alphaStageOffset (q := q) (N := J.tupleWidth)
            (alphaCellToMoveIndex F x).2.1).castSucc).val =
        (alphaCellCrossingWire F x).val := by
      simpa [z, alphaCellToMoveIndex] using hbefore
    change J.tupleWidth -
      ((alphaCellToMoveIndex F x).1.rev.val +
        ((F.1.2 (alphaCellToMoveIndex F x).1).position
          (alphaStageOffset (q := q) (N := J.tupleWidth)
            (alphaCellToMoveIndex F x).2.1).castSucc).val + 1) =
      x.val.2.val
    rw [hbefore', alphaCellCrossingWire_val]
    have hrowrev : (alphaCellToMoveIndex F x).1.rev.val = x.val.1.rev.val := by
      rfl
    rw [hrowrev]
    have hbound := alphaCell_wire_bound F x
    omega

theorem alphaCellToMoveIndex_right_inverse
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) :
    alphaCellToMoveIndex F (alphaMoveCell F z) = z := by
  rcases z with ⟨a, ⟨u, hu⟩⟩
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply Fin.ext
    have hstage := alphaMoveCell_crossingStage F ⟨a, ⟨u, hu⟩⟩
    change (alphaCellCrossingStage F (alphaMoveCell F ⟨a, ⟨u, hu⟩⟩)).val - q = u.val
    have hstageVal := congrArg Fin.val hstage
    have hval :
        (alphaCellCrossingStage F (alphaMoveCell F ⟨a, ⟨u, hu⟩⟩)).val =
          q + u.val := by
      simpa [alphaStageOffset] using hstageVal
    omega

def alphaMoveCellEquiv
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    AlphaMoveIndex F ≃ (F.intermediate.alphaShape).Cell where
  toFun := alphaMoveCell F
  invFun := alphaCellToMoveIndex F
  left_inv := alphaCellToMoveIndex_right_inverse F
  right_inv := alphaMoveCell_left_inverse F

theorem alphaMoveCellEquiv_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (z : AlphaMoveIndex F) :
    alphaCellEntry F (alphaMoveCellEquiv F z) =
      (alphaStageIndex (N := J.tupleWidth) z.2.1).rev :=
  alphaMoveCell_entry F z

theorem reversePathAlphaProduct_eq_move_product
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) :
    reversePathAlphaProduct (F.1.2 a) =
      @Finset.prod {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u} ℝ
        Real.instCommMonoid
        (@Finset.univ _ (@Subtype.fintype (Fin (p * J.tupleWidth))
          (AlphaMovePredicate F a) (Classical.decPred _) (Fin.fintype _)))
        (fun u => D.alpha (alphaStageIndex (N := J.tupleWidth) u.1).rev) := by
  classical
  unfold reversePathAlphaProduct
  have hfilter := Finset.prod_filter
    (s := (Finset.univ : Finset (Fin (p * J.tupleWidth))))
    (AlphaMovePredicate F a)
    (fun u : Fin (p * J.tupleWidth) => D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev)
  have hpoint : ∀ u : Fin (p * J.tupleWidth),
      (if ((F.1.2 a).position
          (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ).val =
          ((F.1.2 a).position
            (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val then 1
       else D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev) =
        (if AlphaMovePredicate F a u then
          D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev else 1) := by
    intro u
    by_cases hval :
        ((F.1.2 a).position
          (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ).val =
          ((F.1.2 a).position
            (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val
    · have hfin : ¬ AlphaMovePredicate F a u := by
        intro hmove
        exact hmove (Fin.ext hval)
      simp [hval, hfin]
    · have hfin : AlphaMovePredicate F a u := by
        intro heq
        exact hval (congrArg Fin.val heq)
      simp [hval, hfin]
  have hsub2 :
      (∏ u with AlphaMovePredicate F a u,
        D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev) =
        @Finset.prod {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u} ℝ
          Real.instCommMonoid
          (@Finset.univ _ (@Subtype.fintype (Fin (p * J.tupleWidth))
            (AlphaMovePredicate F a) (Classical.decPred _) (Fin.fintype _)))
          (fun u => D.alpha (alphaStageIndex (N := J.tupleWidth) u.1).rev) := by
    exact @Finset.prod_subtype (Fin (p * J.tupleWidth)) ℝ Real.instCommMonoid
      (AlphaMovePredicate F a)
      (@Subtype.fintype (Fin (p * J.tupleWidth)) (AlphaMovePredicate F a)
        (Classical.decPred _) (Fin.fintype _))
      ((Finset.univ : Finset (Fin (p * J.tupleWidth))).filter
        (AlphaMovePredicate F a))
      (by intro u; simp)
      (fun u : Fin (p * J.tupleWidth) =>
        D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev)
  calc
    (∏ u : Fin (p * J.tupleWidth),
        (if ((F.1.2 a).position
          (alphaStageOffset (q := q) (N := J.tupleWidth) u).succ).val =
            ((F.1.2 a).position
              (alphaStageOffset (q := q) (N := J.tupleWidth) u).castSucc).val then 1
         else D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev)) =
        (∏ u : Fin (p * J.tupleWidth),
          (if AlphaMovePredicate F a u then
            D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev else 1)) := by
          apply Finset.prod_congr rfl
          intro u hu
          exact hpoint u
    _ = ∏ u with AlphaMovePredicate F a u,
          D.alpha (alphaStageIndex (N := J.tupleWidth) u).rev := hfilter.symm
    _ = @Finset.prod {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u} ℝ
          Real.instCommMonoid
          (@Finset.univ _ (@Subtype.fintype (Fin (p * J.tupleWidth))
            (AlphaMovePredicate F a) (Classical.decPred _) (Fin.fintype _)))
          (fun u => D.alpha (alphaStageIndex (N := J.tupleWidth) u.1).rev) := hsub2

theorem tuplePathFamily_alpha_product_eq
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    (∏ a : Fin r, reversePathAlphaProduct (F.1.2 a)) =
      ∏ x : (F.intermediate.alphaShape).Cell,
        D.alpha (alphaCellEntry F x) := by
  classical
  have hrow : ∀ a : Fin r,
      reversePathAlphaProduct (F.1.2 a) =
        ∏ u : {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u},
          D.alpha (alphaStageIndex (N := J.tupleWidth) u.1).rev := by
    intro a
    exact reversePathAlphaProduct_eq_move_product F a
  calc
    (∏ a : Fin r, reversePathAlphaProduct (F.1.2 a)) =
        ∏ a : Fin r, ∏ u : {u : Fin (p * J.tupleWidth) // AlphaMovePredicate F a u},
          D.alpha (alphaStageIndex (N := J.tupleWidth) u.1).rev := by
      apply Finset.prod_congr rfl
      intro a ha
      exact hrow a
    _ = ∏ z : AlphaMoveIndex F,
        D.alpha (alphaStageIndex (N := J.tupleWidth) z.2.1).rev := by
      symm
      exact Fintype.prod_sigma
        (fun z : AlphaMoveIndex F =>
          D.alpha (alphaStageIndex (N := J.tupleWidth) z.2.1).rev)
    _ = ∏ x : (F.intermediate.alphaShape).Cell,
        D.alpha (alphaCellEntry F x) := by
      apply Fintype.prod_equiv (alphaMoveCellEquiv F)
      intro z
      rw [alphaMoveCellEquiv_entry]

theorem tuplePathFamilyWeightBridge_of_pathFamily
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    TuplePathFamilyWeightBridge F :=
  { beta_product_eq := tuplePathFamily_beta_product_eq F
    alpha_product_eq := tuplePathFamily_alpha_product_eq F }

theorem tupleCoproductTableauOfPathFamily_weight_eq_pathFamilyWeight_unconditional
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    tupleCoproductWeight D I J hstruct (tupleCoproductTableauOfPathFamily F) =
      ∏ a : Fin r, (F.1.2 a).weight :=
  tupleCoproductTableauOfPathFamily_weight_eq_pathFamilyWeight F
    (tuplePathFamilyWeightBridge_of_pathFamily F)

theorem tupleNetwork_good_signedWeight_eq_canonicalTableauWeight
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleVertexDisjointPathFamily D I J hstruct) :
    networkTermSignedWeight T.1 =
      tupleCoproductWeight D I J hstruct
        (tupleCoproductTableauOfPathFamily T) := by
  unfold networkTermSignedWeight
  have hsign : T.1.1.sign = 1 := by
    simpa using congrArg Equiv.Perm.sign (tupleNetwork_good_perm_eq_refl T.1 T.2)
  rw [hsign]
  norm_num
  exact (tupleCoproductTableauOfPathFamily_weight_eq_pathFamilyWeight_unconditional T).symm

end

end ToeplitzPositroids.Edrei
