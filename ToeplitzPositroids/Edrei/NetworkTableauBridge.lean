import ToeplitzPositroids.Edrei.FiniteFactorNetworkTableau
import ToeplitzPositroids.Edrei.FiniteFactorNetworkWeights
import ToeplitzPositroids.Edrei.SkewTableauFromTuple

/-!
# The first layer of the network/tableau correspondence

This file begins the concrete correspondence used by the finite `gamma = 0` expansion.  A legal
unit-step path crosses each wire between its endpoints exactly once; the crossing stage is the
canonical datum from which a tableau entry is read.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- The network wire immediately below a cell in reflected row coordinates. -/
def reflectedCellWire {r N : ℕ} (a : Fin r) (c : Fin N)
    (hbound : a.rev.val + c.val + 1 ≤ N) : Fin (N + 1) :=
  ⟨N - (a.rev.val + c.val + 1), by omega⟩

@[simp]
theorem reflectedCellWire_val {r N : ℕ} (a : Fin r) (c : Fin N)
    (hbound : a.rev.val + c.val + 1 ≤ N) :
    (reflectedCellWire a c hbound).val = N - (a.rev.val + c.val + 1) :=
  rfl

theorem reflected_cell_wire_le_of_part_lt
    {N a x c : ℕ} (hpart : c < N - (a + x)) :
    x ≤ N - (a + (c + 1)) := by
  by_cases hax : a + x ≤ N
  · have hcancel : N - (a + x) + (a + x) = N := Nat.sub_add_cancel hax
    omega
  · have hzero : N - (a + x) = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hax)
    exfalso
    simp [hzero] at hpart

theorem reflected_cell_wire_lt_of_part_le
    {N a x c : ℕ} (hac : a + c + 1 < N)
    (hpart : N - (a + x) ≤ c) :
    N - (a + (c + 1)) < x := by
  by_cases hax : a + x ≤ N
  · have hcancel : N - (a + x) + (a + x) = N := Nat.sub_add_cancel hax
    have hbc : a + (c + 1) ≤ N := by omega
    rw [Nat.sub_lt_iff_lt_add hbc]
    omega
  · have hle : N - (a + (c + 1)) ≤ N - a := by
      apply Nat.sub_le_sub_left
      omega
    have hlt : N - a < x := by omega
    exact hle.trans_lt hlt

theorem alphaCell_wire_bound
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    x.val.1.rev.val + x.val.2.val + 1 ≤ J.tupleWidth := by
  have hx := FiniteSkewShape.mem_cells.mp x.property
  have hmiddle := F.intermediate.outer_ge x.val.1
  have hxouter : x.val.2.val < F.intermediate.middle x.val.1 := by
    simpa [IntermediateRectanglePartition.alphaShape] using hx.2
  have houterEq : containingOuterPartition J x.val.1 =
      J x.val.1.rev - (x.val.1.rev.val + 1) := rfl
  rw [houterEq] at hmiddle
  have hJ := J.value_le_tupleWidth x.val.1.rev
  have hpos := J.position_le x.val.1.rev
  omega

theorem betaCell_wire_bound
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    x.val.1.rev.val + x.val.2.val + 1 ≤ J.tupleWidth := by
  have hx := FiniteSkewShape.mem_cells.mp x.property
  have hxouter : x.val.2.val < containingOuterPartition J x.val.1 := by
    simpa [IntermediateRectanglePartition.betaShape] using hx.2
  change x.val.2.val < J x.val.1.rev - (x.val.1.rev.val + 1) at hxouter
  have hJ := J.value_le_tupleWidth x.val.1.rev
  have hpos := J.position_le x.val.1.rev
  omega

/-- The wire crossed by an alpha cell of a reflected path family. -/
def alphaCellCrossingWire
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) : Fin (J.tupleWidth + 1) :=
  reflectedCellWire x.val.1 x.val.2 (alphaCell_wire_bound F x)

@[simp]
theorem alphaCellCrossingWire_val
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (alphaCellCrossingWire F x).val =
      J.tupleWidth - (x.val.1.rev.val + x.val.2.val + 1) :=
  rfl

/-- The wire crossed by a beta cell of a reflected path family. -/
def betaCellCrossingWire
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) : Fin (J.tupleWidth + 1) :=
  reflectedCellWire x.val.1 x.val.2 (betaCell_wire_bound F x)

@[simp]
theorem betaCellCrossingWire_val
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    (betaCellCrossingWire F x).val =
      J.tupleWidth - (x.val.1.rev.val + x.val.2.val + 1) :=
  rfl

theorem alphaCell_crossing_bounds
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (tupleNetworkSource J (F.1.1 x.val.1)).val ≤
        (alphaCellCrossingWire F x).val ∧
      (alphaCellCrossingWire F x).val <
        (tupleNetworkSink I J hstruct x.val.1).val ∧
      ((F.1.2 x.val.1).position
        (betaBoundaryVertex p q J.tupleWidth)).val ≤
        (alphaCellCrossingWire F x).val := by
  let a := x.val.1
  let c := x.val.2
  let P := F.1.2 a
  let v := betaBoundaryVertex p q J.tupleWidth
  have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
  have ha : F.1.1 a = a := by rw [hperm]; rfl
  have hx := FiniteSkewShape.mem_cells.mp x.property
  have hxinner : containedInnerPartition I J hstruct a ≤ c.val := by
    simpa [IntermediateRectanglePartition.alphaShape, a, c] using hx.1
  have hxmiddle : c.val < F.intermediate.middle a := by
    simpa [IntermediateRectanglePartition.alphaShape, a, c] using hx.2
  have hmiddleOuter := F.intermediate.outer_ge a
  have houterEq : containingOuterPartition J a =
      J a.rev - (a.rev.val + 1) := rfl
  rw [houterEq] at hmiddleOuter
  have hac : a.rev.val + c.val + 1 < J.tupleWidth := by
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hmid : F.intermediate.middle a =
      J.tupleWidth - (a.rev.val + (P.position v).val) := by
    rfl
  have hinnerEq : containedInnerPartition I J hstruct a =
      J.tupleWidth - (a.rev.val +
        (tupleNetworkSink I J hstruct a).val) := by
    symm
    exact reflectedWirePart_sink I J hstruct a
  have hsource := P.source_le_position v
  have hsink := P.position_le_sink v
  change (tupleNetworkSource J (F.1.1 a)).val ≤ (P.position v).val at hsource
  change (P.position v).val ≤ (tupleNetworkSink I J hstruct a).val at hsink
  have hsourceA : (tupleNetworkSource J a).val ≤ (P.position v).val := by
    simpa [ha] using hsource
  rw [hinnerEq] at hxinner
  constructor
  · change (tupleNetworkSource J (F.1.1 a)).val ≤
      J.tupleWidth - (a.rev.val + (c.val + 1))
    have hxmiddle' : c.val < J.tupleWidth -
        (a.rev.val + (P.position v).val) := by
      simpa [hmid] using hxmiddle
    have hle := reflected_cell_wire_le_of_part_lt hxmiddle'
    have hsourceF : (tupleNetworkSource J (F.1.1 a)).val ≤
        (tupleNetworkSource J a).val := by
      rw [ha]
    exact hsourceF.trans (hsourceA.trans hle)
  constructor
  · change J.tupleWidth - (a.rev.val + (c.val + 1)) <
      (tupleNetworkSink I J hstruct a).val
    change J.tupleWidth - (a.rev.val +
      (tupleNetworkSink I J hstruct a).val) ≤ c.val at hxinner
    exact reflected_cell_wire_lt_of_part_le hac hxinner
  · change (P.position v).val ≤ J.tupleWidth - (a.rev.val + (c.val + 1))
    have hxmiddle' : c.val < J.tupleWidth - (a.rev.val + (P.position v).val) := by
      simpa [hmid] using hxmiddle
    exact reflected_cell_wire_le_of_part_lt hxmiddle'

theorem betaCell_crossing_bounds
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    (tupleNetworkSource J (F.1.1 x.val.1)).val ≤
        (betaCellCrossingWire F x).val ∧
      (betaCellCrossingWire F x).val <
        (tupleNetworkSink I J hstruct x.val.1).val ∧
      (betaCellCrossingWire F x).val <
        ((F.1.2 x.val.1).position
          (betaBoundaryVertex p q J.tupleWidth)).val := by
  let a := x.val.1
  let c := x.val.2
  let P := F.1.2 a
  let v := betaBoundaryVertex p q J.tupleWidth
  have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
  have ha : F.1.1 a = a := by rw [hperm]; rfl
  have hx := FiniteSkewShape.mem_cells.mp x.property
  have hxmiddle : F.intermediate.middle a ≤ c.val := by
    simpa [IntermediateRectanglePartition.betaShape, a, c] using hx.1
  have hxouter : c.val < containingOuterPartition J a := by
    simpa [IntermediateRectanglePartition.betaShape, a, c] using hx.2
  have hmid : F.intermediate.middle a =
      J.tupleWidth - (a.rev.val + (P.position v).val) := by
    rfl
  have hsink := P.position_le_sink v
  change (P.position v).val ≤ (tupleNetworkSink I J hstruct a).val at hsink
  have houterEq : containingOuterPartition J a =
      J a.rev - (a.rev.val + 1) := rfl
  rw [houterEq] at hxouter
  have hac : a.rev.val + c.val + 1 < J.tupleWidth := by
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hxmiddlePart : J.tupleWidth -
      (a.rev.val + (P.position v).val) ≤ c.val := by
    simpa [hmid] using hxmiddle
  have hcrossBefore : J.tupleWidth - (a.rev.val + (c.val + 1)) <
      (P.position v).val :=
    reflected_cell_wire_lt_of_part_le hac hxmiddlePart
  constructor
  · rw [ha]
    change (tupleNetworkSource J a).val ≤
      J.tupleWidth - (a.rev.val + (c.val + 1))
    change J.tupleWidth - (J a.rev - 1) ≤
      J.tupleWidth - (a.rev.val + (c.val + 1))
    omega
  constructor
  · change J.tupleWidth - (a.rev.val + (c.val + 1)) <
      (tupleNetworkSink I J hstruct a).val
    exact hcrossBefore.trans_le hsink
  · change J.tupleWidth - (a.rev.val + (c.val + 1)) < (P.position v).val
    exact hcrossBefore

/-- The unique stage at which a path crosses a prescribed wire. -/
noncomputable def FiniteFactorPath.crossingStage
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (k : ℕ) (hsource : source.val ≤ k) (hsink : k < sink.val) :
    Fin (finiteFactorStageCount p q N) :=
  Classical.choose (P.existsUnique_step_at_wire k hsource hsink).exists

theorem FiniteFactorPath.crossingStage_spec
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (k : ℕ) (hsource : source.val ≤ k) (hsink : k < sink.val) :
    (P.position (P.crossingStage k hsource hsink).castSucc).val = k ∧
      (P.position (P.crossingStage k hsource hsink).succ).val = k + 1 := by
  exact Classical.choose_spec (P.existsUnique_step_at_wire k hsource hsink).exists

theorem FiniteFactorPath.crossingStage_unique
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (k : ℕ) (hsource : source.val ≤ k) (hsink : k < sink.val)
    {t : Fin (finiteFactorStageCount p q N)}
    (ht : (P.position t.castSucc).val = k ∧
      (P.position t.succ).val = k + 1) :
    t = P.crossingStage k hsource hsink := by
  exact (P.existsUnique_step_at_wire k hsource hsink).unique ht
    (P.crossingStage_spec k hsource hsink)

theorem FiniteFactorPath.crossingStage_le_of_wire_le
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    {k₁ k₂ : ℕ} (hsource₁ : source.val ≤ k₁) (hsink₁ : k₁ < sink.val)
    (hsource₂ : source.val ≤ k₂) (hsink₂ : k₂ < sink.val)
    (hwire : k₁ ≤ k₂) :
    P.crossingStage k₁ hsource₁ hsink₁ ≤
      P.crossingStage k₂ hsource₂ hsink₂ := by
  by_contra hnot
  have hlt : (P.crossingStage k₂ hsource₂ hsink₂).val <
      (P.crossingStage k₁ hsource₁ hsink₁).val := by omega
  have hvertex : (P.crossingStage k₂ hsource₂ hsink₂).succ ≤
      (P.crossingStage k₁ hsource₁ hsink₁).castSucc := by
    change (P.crossingStage k₂ hsource₂ hsink₂).val + 1 ≤
      (P.crossingStage k₁ hsource₁ hsink₁).val
    omega
  have hmono := P.position_monotone hvertex
  change (P.position (P.crossingStage k₂ hsource₂ hsink₂).succ).val ≤
      (P.position (P.crossingStage k₁ hsource₁ hsink₁).castSucc).val at hmono
  have hspec₁ := P.crossingStage_spec k₁ hsource₁ hsink₁
  have hspec₂ := P.crossingStage_spec k₂ hsource₂ hsink₂
  omega

theorem FiniteFactorPath.crossingStage_lt_of_wire_lt
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    {k₁ k₂ : ℕ} (hsource₁ : source.val ≤ k₁) (hsink₁ : k₁ < sink.val)
    (hsource₂ : source.val ≤ k₂) (hsink₂ : k₂ < sink.val)
    (hwire : k₁ < k₂) :
    P.crossingStage k₁ hsource₁ hsink₁ <
      P.crossingStage k₂ hsource₂ hsink₂ := by
  have hle := P.crossingStage_le_of_wire_le hsource₁ hsink₁
    hsource₂ hsink₂ hwire.le
  have hne : P.crossingStage k₁ hsource₁ hsink₁ ≠
      P.crossingStage k₂ hsource₂ hsink₂ := by
    intro heq
    have hspec₁ := P.crossingStage_spec k₁ hsource₁ hsink₁
    have hspec₂ := P.crossingStage_spec k₂ hsource₂ hsink₂
    have hcur := congrArg (fun s ↦ (P.position s.castSucc).val) heq
    change (P.position (P.crossingStage k₁ hsource₁ hsink₁).castSucc).val =
      (P.position (P.crossingStage k₂ hsource₂ hsink₂).castSucc).val at hcur
    rw [hspec₁.1, hspec₂.1] at hcur
    omega
  exact lt_of_le_of_ne hle hne

/-- The crossing stage of a beta cell in a good reflected path family. -/
noncomputable def betaCellCrossingStage
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    Fin (finiteFactorStageCount p q J.tupleWidth) :=
  (F.1.2 x.val.1).crossingStage (betaCellCrossingWire F x).val
    (betaCell_crossing_bounds F x).1
    (betaCell_crossing_bounds F x).2.1

theorem betaCellCrossingStage_spec
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    ((F.1.2 x.val.1).position (betaCellCrossingStage F x).castSucc).val =
        (betaCellCrossingWire F x).val ∧
      ((F.1.2 x.val.1).position (betaCellCrossingStage F x).succ).val =
        (betaCellCrossingWire F x).val + 1 := by
  exact (F.1.2 x.val.1).crossingStage_spec
    (betaCellCrossingWire F x).val
    (betaCell_crossing_bounds F x).1
    (betaCell_crossing_bounds F x).2.1

/-- The crossing stage of an alpha cell in a good reflected path family. -/
noncomputable def alphaCellCrossingStage
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    Fin (finiteFactorStageCount p q J.tupleWidth) :=
  (F.1.2 x.val.1).crossingStage (alphaCellCrossingWire F x).val
    (alphaCell_crossing_bounds F x).1
    (alphaCell_crossing_bounds F x).2.1

theorem alphaCellCrossingStage_spec
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    ((F.1.2 x.val.1).position (alphaCellCrossingStage F x).castSucc).val =
        (alphaCellCrossingWire F x).val ∧
      ((F.1.2 x.val.1).position (alphaCellCrossingStage F x).succ).val =
        (alphaCellCrossingWire F x).val + 1 := by
  exact (F.1.2 x.val.1).crossingStage_spec
    (alphaCellCrossingWire F x).val
    (alphaCell_crossing_bounds F x).1
    (alphaCell_crossing_bounds F x).2.1

theorem betaCellCrossingStage_lt_q
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
  (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    (betaCellCrossingStage F x).val < q := by
  have hspec := betaCellCrossingStage_spec F x
  have hbefore := betaCell_crossing_bounds F x
  by_contra hbad
  have hq : q ≤ (betaCellCrossingStage F x).val := by omega
  have hvertex : betaBoundaryVertex p q J.tupleWidth ≤
      (betaCellCrossingStage F x).castSucc := by
    change q ≤ (betaCellCrossingStage F x).val
    exact hq
  have hmono := (F.1.2 x.val.1).position_monotone hvertex
  change ((F.1.2 x.val.1).position
      (betaBoundaryVertex p q J.tupleWidth)).val ≤
      ((F.1.2 x.val.1).position
        (betaCellCrossingStage F x).castSucc).val at hmono
  omega

theorem alphaCellCrossingStage_ge_q
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    q ≤ (alphaCellCrossingStage F x).val := by
  have hspec := alphaCellCrossingStage_spec F x
  have hbefore := alphaCell_crossing_bounds F x
  by_contra hbad
  have htq : (alphaCellCrossingStage F x).val + 1 ≤ q := by omega
  have hvertex : (alphaCellCrossingStage F x).succ ≤
      betaBoundaryVertex p q J.tupleWidth := by
    change (alphaCellCrossingStage F x).val + 1 ≤ q
    exact htq
  have hmono := (F.1.2 x.val.1).position_monotone hvertex
  change ((F.1.2 x.val.1).position
      (alphaCellCrossingStage F x).succ).val ≤
      ((F.1.2 x.val.1).position
        (betaBoundaryVertex p q J.tupleWidth)).val at hmono
  omega

theorem alphaCellCrossingStage_block_lt_p
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (alphaCellCrossingStage F x).val < q + p * J.tupleWidth ∧
      (alphaCellCrossingStage F x).val - q < p * J.tupleWidth := by
  have ht := (alphaCellCrossingStage F x).isLt
  change (alphaCellCrossingStage F x).val < q + p * J.tupleWidth at ht
  constructor
  · change (alphaCellCrossingStage F x).val < q + p * J.tupleWidth at ht
    exact ht
  · have hq := alphaCellCrossingStage_ge_q F x
    omega

theorem alphaCellCrossingStage_alpha_index_lt_p
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (alphaCellCrossingStage F x).val - q < p * J.tupleWidth := by
  exact (alphaCellCrossingStage_block_lt_p F x).2

theorem alphaCellCrossingStage_alpha_index_bound
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    ((alphaCellCrossingStage F x).val - q) / J.tupleWidth < p := by
  let P := F.1.2 x.val.1
  let t := alphaCellCrossingStage F x
  have htq := alphaCellCrossingStage_ge_q F x
  have hvalid := P.valid t
  unfold NetworkStepAllowed at hvalid
  rw [if_neg (by omega : ¬t.val < q)] at hvalid
  have hspec := alphaCellCrossingStage_spec F x
  have hspec' :
      (P.position t.castSucc).val = (alphaCellCrossingWire F x).val ∧
        (P.position t.succ).val = (alphaCellCrossingWire F x).val + 1 := by
    simpa [t, P] using hspec
  rcases hvalid with hstay | hmove
  · exfalso
    omega
  · simpa [t, P] using hmove.1

theorem alphaCellCrossingStage_decomposition
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (alphaCellCrossingStage F x).val =
      q + (((alphaCellCrossingStage F x).val - q) / J.tupleWidth) * J.tupleWidth +
        (alphaCellCrossingWire F x).val := by
  let P := F.1.2 x.val.1
  let t := alphaCellCrossingStage F x
  let k := (alphaCellCrossingWire F x).val
  have htq := alphaCellCrossingStage_ge_q F x
  have hN : 0 < J.tupleWidth := by
    have hc := x.val.2.isLt
    omega
  have hvalid := P.valid t
  unfold NetworkStepAllowed at hvalid
  rw [if_neg (by omega : ¬t.val < q)] at hvalid
  have hspec := alphaCellCrossingStage_spec F x
  have hspec' :
      (P.position t.castSucc).val = k ∧
        (P.position t.succ).val = k + 1 := by
    simpa [t, P, k] using hspec
  rcases hvalid with hstay | hmove
  · exfalso
    omega
  · have hrem0 := hmove.2.1
    change (P.position t.castSucc).val = (t.val - q) % J.tupleWidth at hrem0
    have hrem : (t.val - q) % J.tupleWidth = k := by
      omega
    have hdecomp := Nat.div_add_mod' (t.val - q) J.tupleWidth
    have hgoal : t.val =
        q + ((t.val - q) / J.tupleWidth) * J.tupleWidth + k := by
      omega
    simpa [t, k] using hgoal

noncomputable def alphaCellEntry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) : Fin p :=
  (⟨((alphaCellCrossingStage F x).val - q) /
      J.tupleWidth, alphaCellCrossingStage_alpha_index_bound F x⟩ : Fin p).rev

noncomputable def betaCellEntry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) : Fin q :=
  (⟨(betaCellCrossingStage F x).val, betaCellCrossingStage_lt_q F x⟩ : Fin q).rev

theorem alphaCellEntry_le_of_stage_le
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.alphaShape).Cell}
    (hstage : alphaCellCrossingStage F y ≤ alphaCellCrossingStage F x) :
    alphaCellEntry F x ≤ alphaCellEntry F y := by
  unfold alphaCellEntry
  apply Fin.rev_le_rev.mpr
  apply Fin.mk_le_mk.mpr
  have hxq := alphaCellCrossingStage_ge_q F x
  have hyq := alphaCellCrossingStage_ge_q F y
  have hsub : (alphaCellCrossingStage F y).val - q ≤
      (alphaCellCrossingStage F x).val - q := by omega
  exact Nat.div_le_div_right hsub

theorem betaCellEntry_lt_of_stage_lt
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.betaShape).Cell}
    (hstage : betaCellCrossingStage F y < betaCellCrossingStage F x) :
    betaCellEntry F x < betaCellEntry F y := by
  unfold betaCellEntry
  apply Fin.rev_lt_rev.mpr
  exact hstage

theorem alphaCellEntry_row_weak
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.alphaShape).Cell}
    (hrow : x.val.1 = y.val.1) (hcol : x.val.2.val ≤ y.val.2.val) :
    alphaCellEntry F x ≤ alphaCellEntry F y := by
  let y' : (F.intermediate.alphaShape).Cell :=
    ⟨(x.val.1, y.val.2), by
      have hy := FiniteSkewShape.mem_cells.mp y.property
      simpa [hrow] using hy⟩
  have hyEq : y' = y := by
    apply Subtype.ext
    simp [y', hrow]
  have hwire : (alphaCellCrossingWire F y').val ≤
      (alphaCellCrossingWire F x).val := by
    rw [alphaCellCrossingWire_val, alphaCellCrossingWire_val]
    have hyrow : y'.val.1 = x.val.1 := by rfl
    have hycol : x.val.2.val ≤ y'.val.2.val := by simpa [y'] using hcol
    rw [hyrow]
    omega
  have hsourceY : (tupleNetworkSource J (F.1.1 x.val.1)).val ≤
      (alphaCellCrossingWire F y').val := by
    simpa [y'] using (alphaCell_crossing_bounds F y').1
  have hsinkY : (alphaCellCrossingWire F y').val <
      (tupleNetworkSink I J hstruct x.val.1).val := by
    simpa [y'] using (alphaCell_crossing_bounds F y').2.1
  have hstageRaw :=
    (F.1.2 x.val.1).crossingStage_le_of_wire_le
      hsourceY hsinkY
      (alphaCell_crossing_bounds F x).1
      (alphaCell_crossing_bounds F x).2.1 hwire
  have hstage : alphaCellCrossingStage F y' ≤
      alphaCellCrossingStage F x := by
    simpa [alphaCellCrossingStage, y'] using hstageRaw
  have hentry := alphaCellEntry_le_of_stage_le F hstage
  rw [hyEq] at hentry
  exact hentry

theorem betaCellEntry_row_strict
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.betaShape).Cell}
    (hrow : x.val.1 = y.val.1) (hcol : x.val.2.val < y.val.2.val) :
    betaCellEntry F x < betaCellEntry F y := by
  let y' : (F.intermediate.betaShape).Cell :=
    ⟨(x.val.1, y.val.2), by
      have hy := FiniteSkewShape.mem_cells.mp y.property
      simpa [hrow] using hy⟩
  have hyEq : y' = y := by
    apply Subtype.ext
    simp [y', hrow]
  have hwire : (betaCellCrossingWire F y').val <
      (betaCellCrossingWire F x).val := by
    rw [betaCellCrossingWire_val, betaCellCrossingWire_val]
    have hyrow : y'.val.1 = x.val.1 := by rfl
    have hycol : x.val.2.val < y'.val.2.val := by simpa [y'] using hcol
    rw [hyrow]
    have hboundY := betaCell_wire_bound F y'
    have hsumX : x.val.1.rev.val + x.val.2.val + 1 < J.tupleWidth := by
      have hsumY := hboundY
      rw [hyrow] at hsumY
      omega
    change J.tupleWidth - (x.val.1.rev.val + (y'.val.2.val + 1)) <
      J.tupleWidth - (x.val.1.rev.val + (x.val.2.val + 1))
    apply Nat.sub_lt_sub_left hsumX
    omega
  have hsourceY : (tupleNetworkSource J (F.1.1 x.val.1)).val ≤
      (betaCellCrossingWire F y').val := by
    simpa [y'] using (betaCell_crossing_bounds F y').1
  have hsinkY : (betaCellCrossingWire F y').val <
      (tupleNetworkSink I J hstruct x.val.1).val := by
    simpa [y'] using (betaCell_crossing_bounds F y').2.1
  have hstageRaw :=
    (F.1.2 x.val.1).crossingStage_lt_of_wire_lt
      hsourceY hsinkY
      (betaCell_crossing_bounds F x).1
      (betaCell_crossing_bounds F x).2.1 hwire
  have hstage : betaCellCrossingStage F y' <
      betaCellCrossingStage F x := by
    simpa [betaCellCrossingStage, y'] using hstageRaw
  have hentry := betaCellEntry_lt_of_stage_lt F hstage
  rw [hyEq] at hentry
  exact hentry

theorem alphaCellEntry_column_strict
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.alphaShape).Cell}
    (hcol : x.val.2.val = y.val.2.val) (hrow : x.val.1 < y.val.1) :
    alphaCellEntry F x < alphaCellEntry F y := by
  unfold alphaCellEntry
  apply Fin.rev_lt_rev.mpr
  apply Fin.mk_lt_mk.mpr
  let tx := alphaCellCrossingStage F x
  let ty := alphaCellCrossingStage F y
  have hquot : (ty.val - q) / J.tupleWidth < (tx.val - q) / J.tupleWidth := by
    by_contra hbad
    have hblock : (tx.val - q) / J.tupleWidth ≤
        (ty.val - q) / J.tupleWidth := by omega
    have hmul := Nat.mul_le_mul_right J.tupleWidth hblock
    have hwire : (alphaCellCrossingWire F x).val <
        (alphaCellCrossingWire F y).val := by
      rw [alphaCellCrossingWire_val, alphaCellCrossingWire_val]
      rw [hcol]
      have hrev := Fin.rev_lt_rev.mpr hrow
      have hrevVal : y.val.1.rev.val < x.val.1.rev.val := Fin.mk_lt_mk.mp hrev
      have hsumX := alphaCell_wire_bound F x
      have hsumY := alphaCell_wire_bound F y
      have hrowVal := Fin.mk_lt_mk.mp hrow
      have hsumOrder : y.val.1.rev.val + y.val.2.val + 1 <
          x.val.1.rev.val + y.val.2.val + 1 := by omega
      have hylt : y.val.1.rev.val + y.val.2.val + 1 < J.tupleWidth := by
        omega
      exact Nat.sub_lt_sub_left hylt hsumOrder
    have hstage : tx.val < ty.val := by
      have hxdec := alphaCellCrossingStage_decomposition F x
      have hydec := alphaCellCrossingStage_decomposition F y
      change tx.val = q + ((tx.val - q) / J.tupleWidth) * J.tupleWidth +
        (alphaCellCrossingWire F x).val at hxdec
      change ty.val = q + ((ty.val - q) / J.tupleWidth) * J.tupleWidth +
        (alphaCellCrossingWire F y).val at hydec
      omega
    have hvertex : tx.succ ≤ ty.castSucc := by
      change tx.val + 1 ≤ ty.val
      omega
    have hstrict : StrictMono (fun z : Fin r ↦
        ((F.1.2 z).position tx.succ).val) := by
      intro a b hab
      exact networkTermGood_position_lt_of_sink_strictMono
        (tupleNetworkSink_strictMono I J hstruct) F.1 F.2 hab tx.succ
    have hgap := strictMono_fin_gap hstrict hrow.le
    have hspecX := (alphaCellCrossingStage_spec F x).2
    have hspecY := (alphaCellCrossingStage_spec F y).1
    change ((F.1.2 x.val.1).position tx.succ).val =
      (alphaCellCrossingWire F x).val + 1 at hspecX
    change ((F.1.2 y.val.1).position ty.castSucc).val =
      (alphaCellCrossingWire F y).val at hspecY
    have hmono := (F.1.2 y.val.1).position_monotone hvertex
    change ((F.1.2 y.val.1).position tx.succ).val ≤
      ((F.1.2 y.val.1).position ty.castSucc).val at hmono
    change y.val.1.val - x.val.1.val +
      ((F.1.2 x.val.1).position tx.succ).val ≤
      ((F.1.2 y.val.1).position tx.succ).val at hgap
    have hrowVal := Fin.mk_lt_mk.mp hrow
    have hrevSumX : x.val.1.rev.val + x.val.1.val + 1 = r := by
      change r - (x.val.1.val + 1) + x.val.1.val + 1 = r
      omega
    have hrevSumY : y.val.1.rev.val + y.val.1.val + 1 = r := by
      change r - (y.val.1.val + 1) + y.val.1.val + 1 = r
      omega
    have hsumX := alphaCell_wire_bound F x
    have hAyEq : y.val.1.rev.val + y.val.2.val + 1 +
        (y.val.1.val - x.val.1.val) =
        x.val.1.rev.val + y.val.2.val + 1 := by
      omega
    have hcancelX := Nat.sub_add_cancel hsumX
    have hwireEq : (alphaCellCrossingWire F y).val =
        (alphaCellCrossingWire F x).val +
          (y.val.1.val - x.val.1.val) := by
      rw [alphaCellCrossingWire_val, alphaCellCrossingWire_val, hcol]
      omega
    omega
  exact hquot

theorem betaCellEntry_column_weak
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    {x y : (F.intermediate.betaShape).Cell}
    (hcol : x.val.2.val = y.val.2.val) (hrow : x.val.1 ≤ y.val.1) :
    betaCellEntry F x ≤ betaCellEntry F y := by
  unfold betaCellEntry
  apply Fin.rev_le_rev.mpr
  apply Fin.mk_le_mk.mpr
  by_cases heq : x.val.1 = y.val.1
  · have hxy : x = y := by
      apply Subtype.ext
      apply Prod.ext
      · exact heq
      · apply Fin.ext
        exact hcol
    simp [hxy]
  · have hrowlt : x.val.1 < y.val.1 := lt_of_le_of_ne hrow heq
    let tx := betaCellCrossingStage F x
    let ty := betaCellCrossingStage F y
    have hstage : ty.val ≤ tx.val := by
      by_contra hbad
      have htxlt : tx.val < ty.val := by omega
      have hvertex : tx.succ ≤ ty.castSucc := by
        change tx.val + 1 ≤ ty.val
        omega
      have hstrict : StrictMono (fun z : Fin r ↦
          ((F.1.2 z).position tx.succ).val) := by
        intro a b hab
        exact networkTermGood_position_lt_of_sink_strictMono
          (tupleNetworkSink_strictMono I J hstruct) F.1 F.2 hab tx.succ
      have hgap := strictMono_fin_gap hstrict hrowlt.le
      have hspecX := (betaCellCrossingStage_spec F x).2
      have hspecY := (betaCellCrossingStage_spec F y).1
      change ((F.1.2 x.val.1).position tx.succ).val =
        (betaCellCrossingWire F x).val + 1 at hspecX
      change ((F.1.2 y.val.1).position ty.castSucc).val =
        (betaCellCrossingWire F y).val at hspecY
      have hmono := (F.1.2 y.val.1).position_monotone hvertex
      change ((F.1.2 y.val.1).position tx.succ).val ≤
        ((F.1.2 y.val.1).position ty.castSucc).val at hmono
      change y.val.1.val - x.val.1.val +
        ((F.1.2 x.val.1).position tx.succ).val ≤
        ((F.1.2 y.val.1).position tx.succ).val at hgap
      have hrowVal := Fin.mk_lt_mk.mp hrowlt
      have hrevSumX : x.val.1.rev.val + x.val.1.val + 1 = r := by
        change r - (x.val.1.val + 1) + x.val.1.val + 1 = r
        omega
      have hrevSumY : y.val.1.rev.val + y.val.1.val + 1 = r := by
        change r - (y.val.1.val + 1) + y.val.1.val + 1 = r
        omega
      have hsumX := betaCell_wire_bound F x
      have hsumY := betaCell_wire_bound F y
      have hAyEq : y.val.1.rev.val + y.val.2.val + 1 +
          (y.val.1.val - x.val.1.val) =
          x.val.1.rev.val + y.val.2.val + 1 := by
        omega
      have hcancelX := Nat.sub_add_cancel hsumX
      have hwireEq : (betaCellCrossingWire F y).val =
          (betaCellCrossingWire F x).val +
            (y.val.1.val - x.val.1.val) := by
        rw [betaCellCrossingWire_val, betaCellCrossingWire_val, hcol]
        omega
      omega
    exact hstage

noncomputable def alphaTableauOfPathFamily
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    AlphaSkewTableau F.intermediate.alphaShape p where
  entry := alphaCellEntry F
  row_weak := by
    intro x y hrow hcol
    exact alphaCellEntry_row_weak F hrow hcol
  column_strict := by
    intro x y hcol hrow
    exact alphaCellEntry_column_strict F (Fin.mk.inj hcol) hrow

noncomputable def betaTableauOfPathFamily
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    BetaSkewTableau F.intermediate.betaShape q where
  entry := betaCellEntry F
  row_strict := by
    intro x y hrow hcol
    exact betaCellEntry_row_strict F hrow hcol
  column_weak := by
    intro x y hcol hrow
    exact betaCellEntry_column_weak F (Fin.mk.inj hcol) hrow

noncomputable def tupleCoproductTableauOfPathFamily
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    TupleCoproductTableau (p := p) (q := q) I J hstruct :=
  { intermediate := F.intermediate
    tableaux :=
      { alphaTableau := alphaTableauOfPathFamily F
        betaTableau := betaTableauOfPathFamily F } }

@[simp]
theorem tupleCoproductTableauOfPathFamily_intermediate
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    (tupleCoproductTableauOfPathFamily F).intermediate = F.intermediate :=
  rfl

theorem tupleCoproductTableauOfPathFamily_intermediate_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G) :
    F.intermediate = G.intermediate := by
  apply IntermediateRectanglePartition.middle_injective
  apply RectanglePartition.rowLength_injective
  funext a
  have hmiddle := congrArg
    (fun T : TupleCoproductTableau (p := p) (q := q) I J hstruct ↦
      fun a ↦ T.intermediate.middle a) hT
  have ha := congrFun hmiddle a
  exact Fin.ext ha

theorem tupleCoproductTableauOfPathFamily_boundary_position_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G) (a : Fin r) :
    (F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth) =
      (G.1.2 a).position (betaBoundaryVertex p q J.tupleWidth) := by
  have hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
  have hmiddle : F.intermediate.middle a = G.intermediate.middle a := by
    exact congrArg (fun M ↦ M.middle a) hI
  have hmid_eq :
      J.tupleWidth - (a.rev.val +
        ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val) =
      J.tupleWidth - (a.rev.val +
        ((G.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val) := by
    change J.tupleWidth - (a.rev.val +
        ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val) =
      J.tupleWidth - (a.rev.val +
        ((G.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val) at hmiddle
    exact hmiddle
  have hFpos := (F.1.2 a).position_le_sink (betaBoundaryVertex p q J.tupleWidth)
  have hGpos := (G.1.2 a).position_le_sink (betaBoundaryVertex p q J.tupleWidth)
  change (F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth) ≤
    tupleNetworkSink I J hstruct a at hFpos
  change (G.1.2 a).position (betaBoundaryVertex p q J.tupleWidth) ≤
    tupleNetworkSink I J hstruct a at hGpos
  change ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val ≤
    J.tupleWidth - (I a.rev - 1) at hFpos
  change ((G.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val ≤
    J.tupleWidth - (I a.rev - 1) at hGpos
  have hIpos := I.position_le a.rev
  have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  apply Fin.ext
  omega

/-! Total entry functions avoid dependent transports when comparing two tableaux whose
intermediate partitions are obtained from different path families. -/

def tupleCoproductBetaEntryAt
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (a : Fin r) (c : Fin J.tupleWidth) : Option (Fin q) :=
  if h : (a, c) ∈ T.intermediate.betaShape.cells then
    some (T.tableaux.betaTableau.entry ⟨(a, c), h⟩)
  else none

def tupleCoproductAlphaEntryAt
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (a : Fin r) (c : Fin J.tupleWidth) : Option (Fin p) :=
  if h : (a, c) ∈ T.intermediate.alphaShape.cells then
    some (T.tableaux.alphaTableau.entry ⟨(a, c), h⟩)
  else none

theorem tupleCoproductTableauOfPathFamily_betaEntryAt_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G) :
    (fun a c ↦ tupleCoproductBetaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily F) a c) =
      (fun a c ↦ tupleCoproductBetaEntryAt hstruct
        (tupleCoproductTableauOfPathFamily G) a c) := by
  exact congrArg
    (fun T : TupleCoproductTableau (p := p) (q := q) I J hstruct ↦
      fun a c ↦ tupleCoproductBetaEntryAt hstruct T a c) hT

theorem tupleCoproductTableauOfPathFamily_alphaEntryAt_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G) :
    (fun a c ↦ tupleCoproductAlphaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily F) a c) =
      (fun a c ↦ tupleCoproductAlphaEntryAt hstruct
        (tupleCoproductTableauOfPathFamily G) a c) := by
  exact congrArg
    (fun T : TupleCoproductTableau (p := p) (q := q) I J hstruct ↦
      fun a c ↦ tupleCoproductAlphaEntryAt hstruct T a c) hT

theorem tupleCoproductTableauOfPathFamily_beta_entry_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G)
    (x : (F.intermediate.betaShape).Cell) :
    betaCellEntry F x =
      betaCellEntry G ⟨x.val, by
        rw [← tupleCoproductTableauOfPathFamily_intermediate_injective F G hT]
        exact x.property⟩ := by
  let hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
  let xG : (G.intermediate.betaShape).Cell := ⟨x.val, by
    rw [← hI]
    exact x.property⟩
  have htotal := tupleCoproductTableauOfPathFamily_betaEntryAt_injective F G hT
  have hx := congrFun (congrFun htotal x.val.1) x.val.2
  have hF : tupleCoproductBetaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily F) x.val.1 x.val.2 =
      some (betaCellEntry F x) := by
    have hmem : (x.val.1, x.val.2) ∈
        (tupleCoproductTableauOfPathFamily F).intermediate.betaShape.cells := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using x.property
    rw [tupleCoproductBetaEntryAt, dif_pos hmem]
    rfl
  have hG : tupleCoproductBetaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily G) x.val.1 x.val.2 =
      some (betaCellEntry G xG) := by
    have hmem : (x.val.1, x.val.2) ∈
        (tupleCoproductTableauOfPathFamily G).intermediate.betaShape.cells := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using xG.property
    rw [tupleCoproductBetaEntryAt, dif_pos hmem]
    congr 2
  rw [hF, hG] at hx
  exact Option.some.inj hx

theorem tupleCoproductTableauOfPathFamily_alpha_entry_injective
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (hT : tupleCoproductTableauOfPathFamily F =
      tupleCoproductTableauOfPathFamily G)
    (x : (F.intermediate.alphaShape).Cell) :
    alphaCellEntry F x =
      alphaCellEntry G ⟨x.val, by
        rw [← tupleCoproductTableauOfPathFamily_intermediate_injective F G hT]
        exact x.property⟩ := by
  let hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
  let xG : (G.intermediate.alphaShape).Cell := ⟨x.val, by
    rw [← hI]
    exact x.property⟩
  have htotal := tupleCoproductTableauOfPathFamily_alphaEntryAt_injective F G hT
  have hx := congrFun (congrFun htotal x.val.1) x.val.2
  have hF : tupleCoproductAlphaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily F) x.val.1 x.val.2 =
      some (alphaCellEntry F x) := by
    have hmem : (x.val.1, x.val.2) ∈
        (tupleCoproductTableauOfPathFamily F).intermediate.alphaShape.cells := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using x.property
    rw [tupleCoproductAlphaEntryAt, dif_pos hmem]
    rfl
  have hG : tupleCoproductAlphaEntryAt hstruct
      (tupleCoproductTableauOfPathFamily G) x.val.1 x.val.2 =
      some (alphaCellEntry G xG) := by
    have hmem : (x.val.1, x.val.2) ∈
        (tupleCoproductTableauOfPathFamily G).intermediate.alphaShape.cells := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using xG.property
    rw [tupleCoproductAlphaEntryAt, dif_pos hmem]
    congr 2
  rw [hF, hG] at hx
  exact Option.some.inj hx

@[simp]
theorem tupleCoproductTableauOfPathFamily_alpha_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.alphaShape).Cell) :
    (tupleCoproductTableauOfPathFamily F).tableaux.alphaTableau.entry x =
      alphaCellEntry F x :=
  rfl

@[simp]
theorem tupleCoproductTableauOfPathFamily_beta_entry
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (x : (F.intermediate.betaShape).Cell) :
    (tupleCoproductTableauOfPathFamily F).tableaux.betaTableau.entry x =
      betaCellEntry F x :=
  rfl

def betaStage {p q N : ℕ} (t : Fin q) : Fin (finiteFactorStageCount p q N) :=
  ⟨t.val, by
    simp only [finiteFactorStageCount]
    omega⟩

def alphaStageOffset {p q N : ℕ} (u : Fin (p * N)) :
    Fin (finiteFactorStageCount p q N) :=
  ⟨q + u.val, by
    simp only [finiteFactorStageCount]
    omega⟩

def alphaStageIndex {p N : ℕ} (u : Fin (p * N)) : Fin p :=
  ⟨u.val / N, by
    have hN : 0 < N := by
      by_contra hN
      have hzero : N = 0 := Nat.eq_zero_of_not_pos hN
      have hu := u.isLt
      simp [hzero] at hu
    exact (Nat.div_lt_iff_lt_mul hN).2 u.isLt⟩

def reversePathBetaProduct
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)}
    (P : FiniteFactorPath (reverseFiniteEdreiData D) N source sink) : ℝ :=
  ∏ t : Fin q,
    (if (P.position (betaStage t).succ).val =
        (P.position (betaStage t).castSucc).val then 1
     else D.beta t.rev)

def reversePathAlphaProduct
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)}
    (P : FiniteFactorPath (reverseFiniteEdreiData D) N source sink) : ℝ :=
  ∏ u : Fin (p * N),
    (if (P.position (alphaStageOffset u).succ).val =
        (P.position (alphaStageOffset u).castSucc).val then 1
     else D.alpha (alphaStageIndex u).rev)

def reversePathStepFactor
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)}
    (P : FiniteFactorPath (reverseFiniteEdreiData D) N source sink)
    (t : Fin (finiteFactorStageCount p q N)) : ℝ :=
  if _hstay : (P.position t.succ).val = (P.position t.castSucc).val then 1
  else if ht : t.val < q then (reverseFiniteEdreiData D).beta ⟨t.val, ht⟩
  else if ha : (t.val - q) / N < p then
    (reverseFiniteEdreiData D).alpha ⟨(t.val - q) / N, ha⟩
  else 0

theorem reversePath_weight_eq_beta_mul_alpha
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)}
    (P : FiniteFactorPath (reverseFiniteEdreiData D) N source sink) :
    P.weight = reversePathBetaProduct P * reversePathAlphaProduct P := by
  rw [P.weight_eq_prod_if_move_parameter]
  simp only [finiteFactorStageCount]
  change (∏ t : Fin (q + p * N), reversePathStepFactor P t) = _
  rw [Fin.prod_univ_add]
  unfold reversePathBetaProduct reversePathAlphaProduct
  apply congrArg₂ (· * ·)
  · refine Finset.prod_congr rfl ?_
    intro t _
    have hcast : Fin.castAdd (p * N) t = betaStage t := by
      apply Fin.ext
      rfl
    by_cases hstay :
        (P.position (betaStage t).succ).val =
          (P.position (betaStage t).castSucc).val
    · rw [← hcast]
      simp [reversePathStepFactor]
    · rw [← hcast]
      simp [reversePathStepFactor]
  · refine Finset.prod_congr rfl ?_
    intro u _
    have hcast : Fin.natAdd q u = alphaStageOffset (q := q) u := by
      apply Fin.ext
      rfl
    by_cases hstay :
        (P.position (alphaStageOffset (q := q) u).succ).val =
          (P.position (alphaStageOffset (q := q) u).castSucc).val
    · rw [← hcast]
      have hstay' :
          (P.position (Fin.natAdd q u).succ).val =
            (P.position (Fin.natAdd q u).castSucc).val := by
        rw [hcast]
        exact hstay
      simp only [reversePathStepFactor]
      split <;> simp_all
    · have hnot : ¬(alphaStageOffset (q := q) u).val < q := by
        change ¬q + u.val < q
        omega
      have huindex : ((alphaStageOffset (q := q) u).val - q) / N =
          (alphaStageIndex u).val := by
        change (q + u.val - q) / N = u.val / N
        rw [Nat.add_sub_cancel_left]
      rw [← hcast]
      have hstay' : ¬(
          (P.position (Fin.natAdd q u).succ).val =
            (P.position (Fin.natAdd q u).castSucc).val) := by
        intro h
        apply hstay
        rw [hcast] at h
        exact h
      simp only [reversePathStepFactor]
      have hindex := (alphaStageIndex u).isLt
      split <;> simp_all [alphaStageIndex]

/-! The remaining weighted part of the correspondence is now isolated in two row-product
identities.  The definitions above already provide the canonical tableau associated with a good
family; this package records exactly the additional identities needed to identify its monomial.
-/
structure TuplePathFamilyWeightBridge
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) where
  beta_product_eq :
    (∏ a : Fin r, reversePathBetaProduct (F.1.2 a)) =
      ∏ x : (F.intermediate.betaShape).Cell,
        D.beta (betaCellEntry F x)
  alpha_product_eq :
    (∏ a : Fin r, reversePathAlphaProduct (F.1.2 a)) =
      ∏ x : (F.intermediate.alphaShape).Cell,
        D.alpha (alphaCellEntry F x)

theorem tupleCoproductTableauOfPathFamily_weight_eq_pathFamilyWeight
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (B : TuplePathFamilyWeightBridge F) :
    tupleCoproductWeight D I J hstruct (tupleCoproductTableauOfPathFamily F) =
      ∏ a : Fin r, (F.1.2 a).weight := by
  let T := tupleCoproductTableauOfPathFamily F
  calc
    tupleCoproductWeight D I J hstruct T =
        (∏ x : (F.intermediate.alphaShape).Cell,
            D.alpha (alphaCellEntry F x)) *
          (∏ x : (F.intermediate.betaShape).Cell,
            D.beta (betaCellEntry F x)) := by
      rfl
    _ = (∏ a : Fin r, reversePathAlphaProduct (F.1.2 a)) *
          (∏ a : Fin r, reversePathBetaProduct (F.1.2 a)) := by
      rw [B.alpha_product_eq, B.beta_product_eq]
    _ = ∏ a : Fin r,
          (reversePathBetaProduct (F.1.2 a) *
            reversePathAlphaProduct (F.1.2 a)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = ∏ a : Fin r, (F.1.2 a).weight := by
      apply Finset.prod_congr rfl
      intro a _
      rw [reversePath_weight_eq_beta_mul_alpha]

theorem tuple_paths_nonempty_implies_nonempty_tupleCoproduct_via_crossing
    {p q r : ℕ} {D : FiniteEdreiData p q}
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hpaths : Nonempty (TupleVertexDisjointPathFamily D I J hstruct)) :
    Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) := by
  obtain ⟨F⟩ := hpaths
  exact ⟨tupleCoproductTableauOfPathFamily F⟩

end

end ToeplitzPositroids.Edrei
