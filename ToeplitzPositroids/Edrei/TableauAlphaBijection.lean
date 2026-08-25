import ToeplitzPositroids.Edrei.TableauBetaBijection
import ToeplitzPositroids.Edrei.TableauAlphaPath
import ToeplitzPositroids.Edrei.NetworkSupport

/-!
# The one-alpha/no-beta converse slice

The finite network is deterministic when it has one alpha block and no beta block.  This file
formalizes that deterministic path lemma and uses it to isolate the next small slice of the
network/tableau bijection.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

theorem FiniteFactorPath.crossingStage_eq_alphaBlockPath
    {N : ℕ} {D : FiniteEdreiData 1 0}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (P : FiniteFactorPath D N source sink)
    (k : ℕ) (hsource_k : source.val ≤ k) (hsink_k : k < sink.val) :
    P.crossingStage k hsource_k hsink_k =
      (alphaBlockPath D hsource).crossingStage k hsource_k hsink_k := by
  have hPspec := P.crossingStage_spec k hsource_k hsink_k
  have hQspec := (alphaBlockPath D hsource).crossingStage_spec k hsource_k hsink_k
  have hPvalid := P.valid (P.crossingStage k hsource_k hsink_k)
  unfold NetworkStepAllowed at hPvalid
  rw [if_neg (by omega : ¬(P.crossingStage k hsource_k hsink_k).val < 0)] at hPvalid
  rcases hPvalid with hstay | ⟨hblock, hx, hy⟩
  · exact False.elim (by omega)
  · have hN : 0 < N := by
      by_contra hN
      have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
      subst N
      have ht := (P.crossingStage k hsource_k hsink_k).isLt
      omega
    have htlt : (P.crossingStage k hsource_k hsink_k).val < N := by
      simpa [finiteFactorStageCount] using
        (P.crossingStage k hsource_k hsink_k).isLt
    have hmod :
        (P.crossingStage k hsource_k hsink_k).val % N =
          (P.crossingStage k hsource_k hsink_k).val :=
      Nat.mod_eq_of_lt htlt
    have hPstage : (P.crossingStage k hsource_k hsink_k).val = k := by
      simp only [Nat.sub_zero] at hx
      rw [hmod] at hx
      have hspec := hPspec.1
      omega
    have hQvalid := (alphaBlockPath D hsource).valid
      ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k)
    unfold NetworkStepAllowed at hQvalid
    rw [if_neg (by omega : ¬
      ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).val < 0)] at hQvalid
    rcases hQvalid with hQstay | ⟨hQblock, hQx, hQy⟩
    · exact False.elim (by omega)
    · have hQlt :
          ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).val < N := by
        simpa [finiteFactorStageCount] using
          ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).isLt
      have hQmod :
          ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).val % N =
            ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).val :=
        Nat.mod_eq_of_lt hQlt
      have hQstage :
          ((alphaBlockPath D hsource).crossingStage k hsource_k hsink_k).val = k := by
        simp only [Nat.sub_zero] at hQx
        rw [hQmod] at hQx
        have hspec := hQspec.1
        omega
      apply Fin.ext
      omega

theorem FiniteFactorPath.eq_alphaBlockPath
    {N : ℕ} {D : FiniteEdreiData 1 0}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (P : FiniteFactorPath D N source sink) :
    P = alphaBlockPath D hsource := by
  apply FiniteFactorPath.ext_of_crossingStage_eq P (alphaBlockPath D hsource)
  intro k hsource_k hsink_k
  exact P.crossingStage_eq_alphaBlockPath hsource k hsource_k hsink_k

theorem tupleCoproductTableau_subsingleton_p_one_q_zero
    {r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T U : TupleCoproductTableau (p := 1) (q := 0) I J hstruct) :
    T = U := by
  have hmid_eq_outer (V : TupleCoproductTableau (p := 1) (q := 0) I J hstruct) :
      V.intermediate.middle = containingOuterPartition J := by
    apply RectanglePartition.rowLength_injective
    funext a
    apply Fin.ext
    have hfit := V.tableaux.betaTableau.fitsRowBound a
    have hwidth : V.intermediate.betaShape.rowWidth a = 0 := by
      exact Nat.eq_zero_of_le_zero hfit
    have hwidthNat :
        containingOuterPartition J a - V.intermediate.middle a = 0 := by
      simpa [IntermediateRectanglePartition.betaShape,
        FiniteSkewShape.rowWidth_eq_sub] using hwidth
    have hleNat : V.intermediate.middle a ≤ containingOuterPartition J a := by
      exact V.intermediate.outer_ge a
    have hgeNat : containingOuterPartition J a ≤ V.intermediate.middle a :=
      Nat.sub_eq_zero_iff_le.mp hwidthNat
    have hEq : V.intermediate.middle a = containingOuterPartition J a :=
      Nat.le_antisymm hleNat hgeNat
    simpa using hEq
  have hmid : T.intermediate = U.intermediate := by
    apply IntermediateRectanglePartition.middle_injective
    exact (hmid_eq_outer T).trans (hmid_eq_outer U).symm
  cases T with
  | mk TI TP =>
    cases U with
    | mk UI UP =>
      dsimp only at hmid
      subst UI
      have ha : TP.alphaTableau = UP.alphaTableau := by
        apply AlphaSkewTableau.entry_injective
        funext x
        change TP.alphaTableau.entry x = UP.alphaTableau.entry x
        exact Subsingleton.elim _ _
      have hb : TP.betaTableau = UP.betaTableau := by
        apply BetaSkewTableau.entry_injective
        funext x
        exact Fin.elim0 (TP.betaTableau.entry x)
      cases TP
      cases UP
      cases ha
      cases hb
      rfl

theorem tupleNetwork_good_term_eq_alphaTupleTerm_p_one_q_zero
    {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    F.1 = alphaTupleTerm D I J hstruct := by
  have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
  apply networkTerm_ext
  · rw [hperm]
    rfl
  · intro a s
    let P : FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
        (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) :=
      { position := (F.1.2 a).position
        source_eq := by simpa [hperm] using (F.1.2 a).source_eq
        sink_eq := (F.1.2 a).sink_eq
        valid := (F.1.2 a).valid }
    have hP := P.eq_alphaBlockPath (tupleNetworkSource_le_sink I J hstruct a)
    have hpos := congrArg (fun Q => Q.position s) hP
    simpa [P, alphaTupleTerm, alphaTuplePath] using hpos

theorem canonicalGoodTableauMap_bijective_p_one_q_zero
    {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 1 0) :
    Function.Bijective (@canonicalGoodTableauMap 1 0 r D I J hstruct) := by
  constructor
  · intro F G hT
    have hF := tupleNetwork_good_term_eq_alphaTupleTerm_p_one_q_zero D I J hstruct F
    have hG := tupleNetwork_good_term_eq_alphaTupleTerm_p_one_q_zero D I J hstruct G
    apply Subtype.ext
    exact hF.trans hG.symm
  · intro T
    let F : TupleVertexDisjointPathFamily D I J hstruct :=
      ⟨alphaTupleTerm D I J hstruct, alphaTupleTerm_good D I J hstruct hhook⟩
    refine ⟨F, ?_⟩
    exact tupleCoproductTableau_subsingleton_p_one_q_zero
      (canonicalGoodTableauMap F) T

theorem canonicalGoodTableauMap_bijective_p_one_q_zero_of_not_indexHook
    {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hnot : ¬IndexHookInequalities I J 1 0) :
    Function.Bijective (@canonicalGoodTableauMap 1 0 r D I J hstruct) := by
  have hnoDomain : ∀ F : {x : TupleFiniteFactorNetworkTerm D I J hstruct //
      NetworkTermGood x}, False := by
    intro F
    have hpaths : Nonempty (TupleVertexDisjointPathFamily D I J hstruct) := ⟨F⟩
    have hstrip := tuple_paths_nonempty_implies_hasIntermediateStripPartition
      hstruct hpaths
    have htableau : Nonempty (TupleCoproductTableau (p := 1) (q := 0) I J hstruct) := by
      exact (tupleCoproduct_nonempty_iff_hasIntermediateStripPartition I J hstruct).2 hstrip
    exact hnot ((tupleCoproduct_nonempty_iff_indexHook I J hstruct).mp htableau)
  have hnoCodomain : ∀ T : TupleCoproductTableau (p := 1) (q := 0) I J hstruct, False := by
    intro T
    exact hnot ((tupleCoproduct_nonempty_iff_indexHook I J hstruct).mp ⟨T⟩)
  constructor
  · intro F G hFG
    exact False.elim (hnoDomain F)
  · intro T
    exact False.elim (hnoCodomain T)

theorem canonicalGoodTableauMap_bijective_p_one_q_zero_of_structural
    {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Function.Bijective (@canonicalGoodTableauMap 1 0 r D I J hstruct) := by
  by_cases hhook : IndexHookInequalities I J 1 0
  · exact canonicalGoodTableauMap_bijective_p_one_q_zero D I J hstruct hhook
  · exact canonicalGoodTableauMap_bijective_p_one_q_zero_of_not_indexHook
      D I J hstruct hhook

noncomputable def canonicalGoodBijectionBridge_p_one_q_zero
    (D : FiniteEdreiData 1 0) (hgamma : D.gamma = 0) :
    CanonicalGoodBijectionBridge D where
  gamma_eq_zero := hgamma
  bijective _ I J hstruct :=
    canonicalGoodTableauMap_bijective_p_one_q_zero_of_structural D I J hstruct

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_p_one_q_zero
    {r : ℕ} (D : FiniteEdreiData 1 0) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := 1) (q := 0) I J hstruct,
        tupleCoproductWeight D I J hstruct T :=
  finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection hgamma
    (canonicalGoodTableauMap_bijective_p_one_q_zero_of_structural D I J hstruct)

end

end ToeplitzPositroids.Edrei
