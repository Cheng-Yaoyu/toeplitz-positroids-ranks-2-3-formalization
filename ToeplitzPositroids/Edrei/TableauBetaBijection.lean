import ToeplitzPositroids.Edrei.TableauBetaPath
import ToeplitzPositroids.Edrei.NetworkTableauConcreteBridge

/-!
# The `p = 0` inverse tableau construction

This file records the first converse slice of the network/tableau correspondence.  When there
are no alpha variables, a beta tableau reconstructs a good path family row by row, and the
canonical network-to-tableau map is surjective.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

def coproduct_p_zero_family
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) :
    TupleVertexDisjointPathFamily D I J hstruct :=
  ⟨coproduct_p_zero_term D T, coproduct_p_zero_term_good D T⟩

theorem coproduct_p_zero_family_intermediate
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct) :
    (coproduct_p_zero_family D T).intermediate = T.intermediate := by
  apply IntermediateRectanglePartition.middle_injective
  apply RectanglePartition.rowLength_injective
  funext a
  apply Fin.ext
  change (coproduct_p_zero_family D T).intermediate.middle a = T.intermediate.middle a
  have hTmid := coproduct_p_zero_intermediate_eq_inner T
  change reflectedWirePart (N := J.tupleWidth) a
      (((coproduct_p_zero_family D T).1.2 a).position
        (betaBoundaryVertex 0 q J.tupleWidth)) = T.intermediate.middle a
  have hv : betaBoundaryVertex 0 q J.tupleWidth =
      Fin.last (finiteFactorStageCount 0 q J.tupleWidth) := by
    apply Fin.ext
    simp [betaBoundaryVertex, finiteFactorStageCount]
  rw [hv, (coproduct_p_zero_family D T).1.2 a |>.sink_eq,
    reflectedWirePart_sink, hTmid]

theorem coproduct_p_zero_betaCellEntry_eq
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := 0) (q := q) I J hstruct)
    (a : Fin r) (c : BetaRowCell T.tableaux.betaTableau a) :
    betaCellEntry (coproduct_p_zero_family D T) ⟨(a, c.val), by
      rw [coproduct_p_zero_family_intermediate]
      simpa [FiniteSkewShape.rowCells] using c.property⟩ =
      T.tableaux.betaTableau.entry ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩ := by
  let F0 := coproduct_p_zero_family D T
  have hmid := coproduct_p_zero_family_intermediate D T
  let x : (F0.intermediate.betaShape).Cell := ⟨(a, c.val), by
    rw [hmid]
    simpa [FiniteSkewShape.rowCells] using c.property⟩
  let ts : Fin (finiteFactorStageCount 0 q J.tupleWidth) :=
    ⟨(betaRowStage T.tableaux.betaTableau a c).val, by
      simp [finiteFactorStageCount]⟩
  have hwire : (betaCellCrossingWire F0 x).val =
      J.tupleWidth - (a.rev.val + c.val.val + 1) := by
    rw [betaCellCrossingWire_val]
  have hbefore := coproduct_p_zero_term_path_position_before_cell D T a c
  have hafter := betaTableauPath_position_after_cell
    (reverseFiniteEdreiData D) T.tableaux.betaTableau a
    (coproduct_p_zero_beta_row_displacement T a) c
  have hbefore' : ((F0.1.2 a).position ts.castSucc).val =
      (betaCellCrossingWire F0 x).val := by
    change (((coproduct_p_zero_term D T).2 a).position _).val = _
    rw [hbefore, hwire]
  have hafter' : ((F0.1.2 a).position ts.succ).val =
      (betaCellCrossingWire F0 x).val + 1 := by
    have hts : ts.succ =
        (⟨(betaRowStage T.tableaux.betaTableau a c).val + 1, by
          simp [finiteFactorStageCount]⟩ :
          Fin (finiteFactorStageCount 0 q J.tupleWidth + 1)) := by
      apply Fin.ext
      rfl
    rw [hts]
    have hv :
        (⟨(betaRowStage T.tableaux.betaTableau a c).val + 1, by
          simp [finiteFactorStageCount]⟩ :
          Fin (finiteFactorStageCount 0 q J.tupleWidth + 1)) =
        (⟨(betaRowStage T.tableaux.betaTableau a c).val, by
          simp [finiteFactorStageCount]⟩ :
          Fin (finiteFactorStageCount 0 q J.tupleWidth)).succ := by
      apply Fin.ext
      rfl
    rw [hv]
    change (((coproduct_p_zero_term D T).2 a).position _).val = _
    change ((betaTableauPath (reverseFiniteEdreiData D)
      T.tableaux.betaTableau a (coproduct_p_zero_beta_row_displacement T a)).position _).val = _
    rw [hafter, hwire]
    change (J.tupleWidth - (J a.rev - 1)) +
      T.intermediate.betaShape.outer a - c.val.val =
      J.tupleWidth - (a.rev.val + c.val.val + 1) + 1
    have houter : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    rw [houter]
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    have hc := FiniteSkewShape.mem_rowCells.mp c.property
    rw [Nat.add_sub_assoc (by omega)]
    omega
  have hstage : betaCellCrossingStage F0 x = ts := by
    unfold betaCellCrossingStage
    symm
    apply (F0.1.2 a).crossingStage_unique
      (betaCellCrossingWire F0 x).val
      (betaCell_crossing_bounds F0 x).1
      (betaCell_crossing_bounds F0 x).2.1
    exact ⟨hbefore', hafter'⟩
  unfold betaCellEntry
  apply Fin.rev_injective
  simp only [Fin.rev_rev]
  apply Fin.ext
  have hstage_val := congrArg Fin.val hstage
  change (betaCellCrossingStage F0 x).val =
    (T.tableaux.betaTableau.entry ⟨(a, c.val), by
      simpa [FiniteSkewShape.rowCells] using c.property⟩).rev.val
  rw [hstage_val]
  rfl

theorem tupleCoproductTableau_eq_of_intermediate_eq_of_entries_eq
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T U : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hmid : T.intermediate = U.intermediate)
    (halpha : (fun a c => tupleCoproductAlphaEntryAt hstruct T a c) =
      fun a c => tupleCoproductAlphaEntryAt hstruct U a c)
    (hbeta : (fun a c => tupleCoproductBetaEntryAt hstruct T a c) =
      fun a c => tupleCoproductBetaEntryAt hstruct U a c) :
    T = U := by
  cases T with
  | mk TI TP =>
    cases U with
    | mk UI UP =>
      dsimp only at hmid
      subst UI
      simp only [SupersymmetricCoproductTableau.mk.injEq]
      have ha : TP.alphaTableau = UP.alphaTableau := by
        apply AlphaSkewTableau.entry_injective
        funext x
        have h := congrFun (congrFun halpha x.val.1) x.val.2
        unfold tupleCoproductAlphaEntryAt at h
        simp only [dif_pos x.property] at h
        exact Option.some.inj h
      have hb : TP.betaTableau = UP.betaTableau := by
        apply BetaSkewTableau.entry_injective
        funext x
        have h := congrFun (congrFun hbeta x.val.1) x.val.2
        unfold tupleCoproductBetaEntryAt at h
        simp only [dif_pos x.property] at h
        exact Option.some.inj h
      cases TP
      cases UP
      cases ha
      cases hb
      exact ⟨True.intro, HEq.rfl⟩

theorem FiniteFactorPath.ext_of_crossingStage_eq
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)}
    (P Q : FiniteFactorPath D N source sink)
    (hcross : ∀ (k : ℕ) (hsource : source.val ≤ k) (hsink : k < sink.val),
      P.crossingStage k hsource hsink = Q.crossingStage k hsource hsink) :
    P = Q := by
  apply FiniteFactorPath.position_injective
  funext s
  apply Fin.ext
  induction s using Fin.induction with
  | zero => simp [P.source_eq, Q.source_eq]
  | succ t ih =>
      have hP := P.position_step_eq_or_succ t
      have hQ := Q.position_step_eq_or_succ t
      change (P.position t.castSucc).val = (Q.position t.castSucc).val at ih
      change (P.position t.succ).val = (Q.position t.succ).val
      rcases hP with hPstay | hPmove
      · rcases hQ with hQstay | hQmove
        · omega
        · let k := (Q.position t.castSucc).val
          have hsource : source.val ≤ k := by
            exact Q.source_le_position t.castSucc
          have hsink : k < sink.val := by
            have hle := Q.position_le_sink t.succ
            change (Q.position t.succ).val ≤ sink.val at hle
            dsimp [k]
            omega
          have hQstage : t = Q.crossingStage k hsource hsink := by
            apply Q.crossingStage_unique
            exact ⟨rfl, hQmove⟩
          have hPspec := P.crossingStage_spec k hsource hsink
          have hstage := hcross k hsource hsink
          rw [hstage, ← hQstage] at hPspec
          dsimp [k] at hPspec
          omega
      · rcases hQ with hQstay | hQmove
        · let k := (P.position t.castSucc).val
          have hsource : source.val ≤ k := by
            exact P.source_le_position t.castSucc
          have hsink : k < sink.val := by
            have hle := P.position_le_sink t.succ
            change (P.position t.succ).val ≤ sink.val at hle
            dsimp [k]
            omega
          have hPstage : t = P.crossingStage k hsource hsink := by
            apply P.crossingStage_unique
            exact ⟨rfl, hPmove⟩
          have hQspec := Q.crossingStage_spec k hsource hsink
          have hstage := hcross k hsource hsink
          rw [← hstage, ← hPstage] at hQspec
          dsimp [k] at hQspec
          omega
        · omega

theorem canonicalGoodTableauMap_surjective_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Function.Surjective (@canonicalGoodTableauMap 0 q r D I J hstruct) := by
  intro T
  let F0 := coproduct_p_zero_family D T
  refine ⟨F0, ?_⟩
  let U := tupleCoproductTableauOfPathFamily F0
  have hmid : U.intermediate = T.intermediate := by
    exact coproduct_p_zero_family_intermediate D T
  apply tupleCoproductTableau_eq_of_intermediate_eq_of_entries_eq U T hmid
  · funext a c
    by_cases hU : (a, c) ∈ U.intermediate.alphaShape.cells
    · exact Fin.elim0 (U.tableaux.alphaTableau.entry ⟨(a, c), hU⟩)
    · have hT : ¬(a, c) ∈ T.intermediate.alphaShape.cells := by
        intro h
        apply hU
        rw [hmid]
        exact h
      simp [tupleCoproductAlphaEntryAt, hU, hT]
  · funext a c
    by_cases hT : (a, c) ∈ T.intermediate.betaShape.cells
    · have hU : (a, c) ∈ U.intermediate.betaShape.cells := by
        rw [hmid]
        exact hT
      unfold tupleCoproductBetaEntryAt
      rw [dif_pos hU, dif_pos hT]
      congr 1
      let rc : BetaRowCell T.tableaux.betaTableau a := ⟨c, by
        simpa [FiniteSkewShape.rowCells] using hT⟩
      change betaCellEntry F0 ⟨(a, c), hU⟩ =
        T.tableaux.betaTableau.entry ⟨(a, c), hT⟩
      simpa [F0, rc, FiniteSkewShape.rowCells] using
        coproduct_p_zero_betaCellEntry_eq D T a rc
    · have hU : ¬(a, c) ∈ U.intermediate.betaShape.cells := by
        intro h
        apply hT
        rw [← hmid]
        exact h
      simp [tupleCoproductBetaEntryAt, hU, hT]

theorem canonicalGoodTableauMap_injective_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Function.Injective (@canonicalGoodTableauMap 0 q r D I J hstruct) := by
  intro F G hT
  have hpermF := tupleNetwork_good_perm_eq_refl F.1 F.2
  have hpermG := tupleNetwork_good_perm_eq_refl G.1 G.2
  apply Subtype.ext
  apply networkTerm_ext
  · rw [hpermF, hpermG]
  · intro a s
    have hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
    have hTFmid := coproduct_p_zero_intermediate_eq_inner
      (tupleCoproductTableauOfPathFamily F)
    have hFmid : (TupleVertexDisjointPathFamily.intermediate F).middle =
        containedInnerPartition I J hstruct := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using hTFmid
    have hTGmid := coproduct_p_zero_intermediate_eq_inner
      (tupleCoproductTableauOfPathFamily G)
    have hGmid : (TupleVertexDisjointPathFamily.intermediate G).middle =
        containedInnerPartition I J hstruct := by
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using hTGmid
    let PF : FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
        (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) :=
      { position := (F.1.2 a).position
        source_eq := by simpa [hpermF] using (F.1.2 a).source_eq
        sink_eq := (F.1.2 a).sink_eq
        valid := (F.1.2 a).valid }
    let PG : FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
        (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) :=
      { position := (G.1.2 a).position
        source_eq := by simpa [hpermG] using (G.1.2 a).source_eq
        sink_eq := (G.1.2 a).sink_eq
        valid := (G.1.2 a).valid }
    have hcross : ∀ (k : ℕ)
        (hsource : (tupleNetworkSource J a).val ≤ k)
        (hsink : k < (tupleNetworkSink I J hstruct a).val),
        PF.crossingStage k hsource hsink = PG.crossingStage k hsource hsink := by
      intro k hsource hsink
      have hkn : k ≤ J.tupleWidth := by
        have hsink' := (tupleNetworkSink I J hstruct a).isLt
        change J.tupleWidth - (I a.rev - 1) < J.tupleWidth + 1 at hsink'
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIpos := I.position_le a.rev
        omega
      let cval := J.tupleWidth - (a.rev.val + k + 1)
      have hcN : cval < J.tupleWidth := by
        change J.tupleWidth - (a.rev.val + k + 1) < J.tupleWidth
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        have hJ := J.value_le_tupleWidth a.rev
        have hNpos : 0 < J.tupleWidth := by omega
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by
          change k < J.tupleWidth - (I a.rev - 1) at hsink
          have hIpos' := I.position_le a.rev
          have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
          omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      let c : Fin J.tupleWidth := ⟨cval, hcN⟩
      have hcellF :
          (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate F).betaShape.cells := by
        apply FiniteSkewShape.mem_cells.mpr
        change (TupleVertexDisjointPathFamily.intermediate F).middle a ≤ cval ∧
          cval < containingOuterPartition J a
        rw [hFmid]
        change I.associatedPart a ≤ cval ∧ cval < J.associatedPart a
        have hassocI : I.associatedPart a = I a.rev - (a.rev.val + 1) := rfl
        have hassocJ : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
        rw [hassocI, hassocJ]
        change I a.rev - (a.rev.val + 1) ≤
            J.tupleWidth - (a.rev.val + k + 1) ∧
          J.tupleWidth - (a.rev.val + k + 1) <
            J a.rev - (a.rev.val + 1)
        change J.tupleWidth - (J a.rev - 1) ≤ k at hsource
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hI := hstruct a.rev
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        have hJ := J.value_le_tupleWidth a.rev
        omega
      have hcellG :
          (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate G).betaShape.cells := by
        apply FiniteSkewShape.mem_cells.mpr
        change (TupleVertexDisjointPathFamily.intermediate G).middle a ≤ cval ∧
          cval < containingOuterPartition J a
        rw [hGmid]
        change I.associatedPart a ≤ cval ∧ cval < J.associatedPart a
        have hassocI : I.associatedPart a = I a.rev - (a.rev.val + 1) := rfl
        have hassocJ : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
        rw [hassocI, hassocJ]
        change I a.rev - (a.rev.val + 1) ≤
            J.tupleWidth - (a.rev.val + k + 1) ∧
          J.tupleWidth - (a.rev.val + k + 1) <
            J a.rev - (a.rev.val + 1)
        change J.tupleWidth - (J a.rev - 1) ≤ k at hsource
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hI := hstruct a.rev
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        have hJ := J.value_le_tupleWidth a.rev
        omega
      let xF : (TupleVertexDisjointPathFamily.intermediate F).betaShape.Cell :=
        ⟨(a, c), hcellF⟩
      let xG : (TupleVertexDisjointPathFamily.intermediate G).betaShape.Cell :=
        ⟨(a, c), hcellG⟩
      have hwireF : (betaCellCrossingWire F xF).val = k := by
        rw [betaCellCrossingWire_val]
        change J.tupleWidth - (a.rev.val +
          (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      have hwireG : (betaCellCrossingWire G xG).val = k := by
        rw [betaCellCrossingWire_val]
        change J.tupleWidth - (a.rev.val +
          (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      have hentry := tupleCoproductTableauOfPathFamily_beta_entry_injective F G hT xF
      have hentry' : betaCellEntry F xF = betaCellEntry G xG := by
        simpa [xF, xG, hI] using hentry
      have hstageVal : (betaCellCrossingStage F xF).val =
          (betaCellCrossingStage G xG).val := by
        have hrev := Fin.rev_injective hentry'
        simpa using congrArg Fin.val hrev
      have hPFstage : betaCellCrossingStage F xF =
          PF.crossingStage k hsource hsink := by
        apply PF.crossingStage_unique
        have hspec := betaCellCrossingStage_spec F xF
        constructor
        · change ((F.1.2 a).position (betaCellCrossingStage F xF).castSucc).val = k
          calc
            _ = (betaCellCrossingWire F xF).val := by simpa [xF] using hspec.1
            _ = k := hwireF
        · change ((F.1.2 a).position (betaCellCrossingStage F xF).succ).val = k + 1
          calc
            _ = (betaCellCrossingWire F xF).val + 1 := by simpa [xF] using hspec.2
            _ = k + 1 := by rw [hwireF]
      have hPGstage : betaCellCrossingStage G xG =
          PG.crossingStage k hsource hsink := by
        apply PG.crossingStage_unique
        have hspec := betaCellCrossingStage_spec G xG
        constructor
        · change ((G.1.2 a).position (betaCellCrossingStage G xG).castSucc).val = k
          calc
            _ = (betaCellCrossingWire G xG).val := by simpa [xG] using hspec.1
            _ = k := hwireG
        · change ((G.1.2 a).position (betaCellCrossingStage G xG).succ).val = k + 1
          calc
            _ = (betaCellCrossingWire G xG).val + 1 := by simpa [xG] using hspec.2
            _ = k + 1 := by rw [hwireG]
      calc
        PF.crossingStage k hsource hsink = betaCellCrossingStage F xF := hPFstage.symm
        _ = betaCellCrossingStage G xG := Fin.ext hstageVal
        _ = PG.crossingStage k hsource hsink := hPGstage
    have hpath := FiniteFactorPath.ext_of_crossingStage_eq PF PG hcross
    have hpos := congrArg (fun P => P.position s) hpath
    simpa [PF, PG] using hpos

theorem canonicalGoodTableauMap_bijective_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Function.Bijective (@canonicalGoodTableauMap 0 q r D I J hstruct) :=
  ⟨canonicalGoodTableauMap_injective_p_zero D I J hstruct,
    canonicalGoodTableauMap_surjective_p_zero D I J hstruct⟩

noncomputable def canonicalGoodBijectionBridge_p_zero
    {q : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0) :
    CanonicalGoodBijectionBridge D where
  gamma_eq_zero := hgamma
  bijective _ I J hstruct := canonicalGoodTableauMap_bijective_p_zero D I J hstruct

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := 0) (q := q) I J hstruct,
        tupleCoproductWeight D I J hstruct T :=
  finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection hgamma
    (canonicalGoodTableauMap_bijective_p_zero D I J hstruct)

theorem finiteFactorMinor_pos_iff_indexHook_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J 0 q :=
  (canonicalGoodBijectionBridge_p_zero D hgamma).finiteFactorMinor_pos_iff_indexHook I J

end
end ToeplitzPositroids.Edrei
