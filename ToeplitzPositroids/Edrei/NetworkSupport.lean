import ToeplitzPositroids.Edrei.FiniteFactorNetworkTableau
import ToeplitzPositroids.Edrei.FiniteFactorMinor
import ToeplitzPositroids.Edrei.FiniteFactorConcreteBridge
import ToeplitzPositroids.Edrei.BetaNetwork
import ToeplitzPositroids.Edrei.AlphaNetwork
import ToeplitzPositroids.Edrei.TableauSupport

/-!
# Support consequences of disjoint finite-factor paths

This file proves the necessity direction of the zero-gamma support criterion directly from the
reflected network.  A good path family determines the intermediate partition at the beta/alpha
boundary; beta-stage and alpha-stage counting then give its two strip bounds.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- Early beta moves preserve strict path order when both endpoint orders are strict. -/
theorem betaEarlyPosition_strict {x y d e t : ℕ}
    (hxy : x < y) (hend : x + d < y + e) :
    x + min d t < y + min e t := by
  by_cases hde : d ≤ e
  · have hmin : min d t ≤ min e t := by
      exact min_le_min hde le_rfl
    omega
  · have hed : e < d := Nat.lt_of_not_ge hde
    by_cases hdt : d ≤ t
    · by_cases het : e ≤ t
      · rw [Nat.min_eq_left hdt, Nat.min_eq_left het]
        omega
      · have hte : t < e := Nat.lt_of_not_ge het
        rw [Nat.min_eq_left hdt, Nat.min_eq_right (Nat.le_of_lt hte)]
        omega
    · have htd : t < d := Nat.lt_of_not_ge hdt
      by_cases het : e ≤ t
      · rw [Nat.min_eq_right (Nat.le_of_lt htd), Nat.min_eq_left het]
        omega
      · have hte : t < e := Nat.lt_of_not_ge het
        rw [Nat.min_eq_right (Nat.le_of_lt htd), Nat.min_eq_right (Nat.le_of_lt hte)]
        omega

/-- The canonical beta path for one row of a reflected tuple network when `p = 0`. -/
noncomputable def betaTuplePath {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 0 q) (a : Fin r) :
    FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
      (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) := by
  have hsource := tupleNetworkSource_le_sink I J hstruct a
  have hhook_a := hhook a.rev (by omega)
  change J a.rev ≤ I a.rev + q at hhook_a
  have hdisp : (tupleNetworkSink I J hstruct a).val -
      (tupleNetworkSource J a).val ≤ q := by
    rw [tupleNetwork_displacement I J hstruct a]
    omega
  exact betaFactorPath (reverseFiniteEdreiData D) hsource hdisp

@[simp]
theorem betaTuplePath_position {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 0 q) (a : Fin r)
    (s : Fin (finiteFactorStageCount 0 q (tupleNetworkBound J) + 1)) :
    (betaTuplePath D I J hstruct hhook a).position s =
      betaFactorPosition (tupleNetworkSource J a)
        ((tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val)
    (by
          have hsource := tupleNetworkSource_le_sink I J hstruct a
          rw [Nat.add_sub_of_le hsource]
          exact Nat.le_of_lt_succ (tupleNetworkSink I J hstruct a).isLt) s := by
  dsimp [betaTuplePath]
  apply betaFactorPath_position

/-- The identity-permutation term built from the canonical beta paths. -/
noncomputable def betaTupleTerm {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 0 q) :
    TupleFiniteFactorNetworkTerm D I J hstruct :=
  ⟨Equiv.refl (Fin r), fun a ↦ betaTuplePath D I J hstruct hhook a⟩

theorem betaTupleTerm_good {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 0 q) :
    NetworkTermGood (betaTupleTerm D I J hstruct hhook) := by
  intro a b hab s
  have hsource := tupleNetworkSource_strictMono J hab
  have hsink := tupleNetworkSink_strictMono I J hstruct hab
  have hdisp_a := tupleNetwork_displacement I J hstruct a
  have hdisp_b := tupleNetwork_displacement I J hstruct b
  have hpos := betaTuplePath_position D I J hstruct hhook a s
  have hpos' := betaTuplePath_position D I J hstruct hhook b s
  have horder :
      ((tupleNetworkSource J a).val +
        min ((tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val) s.val) <
      ((tupleNetworkSource J b).val +
        min ((tupleNetworkSink I J hstruct b).val - (tupleNetworkSource J b).val) s.val) := by
    apply betaEarlyPosition_strict
    · exact hsource
    · have hsource_a := tupleNetworkSource_le_sink I J hstruct a
      have hsource_b := tupleNetworkSource_le_sink I J hstruct b
      change (tupleNetworkSink I J hstruct a).val <
        (tupleNetworkSink I J hstruct b).val at hsink
      rw [← Nat.add_sub_of_le hsource_a, ← Nat.add_sub_of_le hsource_b] at hsink
      exact hsink
  intro hcollision
  change (betaTuplePath D I J hstruct hhook a).position s =
    (betaTuplePath D I J hstruct hhook b).position s at hcollision
  have hcollisionVal := congrArg Fin.val hcollision
  rw [hpos, hpos'] at hcollisionVal
  apply (Nat.ne_of_lt horder)
  simpa [betaFactorPosition] using hcollisionVal

/-- The canonical path for one row when the finite factor has one alpha block and no beta block.
-/
noncomputable def alphaTuplePath {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) (a : Fin r) :
    FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
      (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) :=
  alphaBlockPath (reverseFiniteEdreiData D) (tupleNetworkSource_le_sink I J hstruct a)

@[simp]
theorem alphaTuplePath_position {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) (a : Fin r)
    (s : Fin (finiteFactorStageCount 1 0 (tupleNetworkBound J) + 1)) :
    (alphaTuplePath D I J hstruct a).position s =
      alphaBlockPosition (tupleNetworkSource J a)
        ((tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val)
        (by
          have hsource := tupleNetworkSource_le_sink I J hstruct a
          rw [Nat.add_sub_of_le hsource]
          exact Nat.le_of_lt_succ (tupleNetworkSink I J hstruct a).isLt) s := by
  dsimp [alphaTuplePath]
  apply alphaBlockPath_position

/-- For `p = 1, q = 0`, the hook inequality separates the endpoint intervals of every two rows.
-/
theorem alpha_hook_endpoint_separation {r : ℕ}
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 1 0)
    {a b : Fin r} (hab : a < b) :
    (tupleNetworkSink I J hstruct a).val < (tupleNetworkSource J b).val := by
  have hrev : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
  let k : Fin r := ⟨a.rev.val - 1, by omega⟩
  have hbk : b.rev ≤ k := by
    change b.rev.val ≤ a.rev.val - 1
    omega
  have hJle : J b.rev ≤ J k := J.strictMono.monotone hbk
  have hhook_a := hhook a.rev (by omega)
  change J k + 1 ≤ I a.rev at hhook_a
  have hJltI : J b.rev < I a.rev := by omega
  change J.tupleWidth - (I a.rev - 1) <
    J.tupleWidth - (J b.rev - 1)
  have hIpos := I.position_le a.rev
  have hJpos := J.position_le b.rev
  have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  have hJbound := J.value_le_tupleWidth b.rev
  omega

/-- The identity-permutation term built from the canonical one-alpha-block paths. -/
noncomputable def alphaTupleTerm {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    TupleFiniteFactorNetworkTerm D I J hstruct :=
  ⟨Equiv.refl (Fin r), fun a ↦ alphaTuplePath D I J hstruct a⟩

theorem alphaTupleTerm_good {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 1 0) :
    NetworkTermGood (alphaTupleTerm D I J hstruct) := by
  intro a b hab s
  have hsep := alpha_hook_endpoint_separation I J hstruct hhook hab
  have hposA := alphaTuplePath_position D I J hstruct a s
  have hposB := alphaTuplePath_position D I J hstruct b s
  have hsourceA := tupleNetworkSource_le_sink I J hstruct a
  have hsourceB := tupleNetworkSource_le_sink I J hstruct b
  have hleA :
      ((alphaTuplePath D I J hstruct a).position s).val ≤
        (tupleNetworkSink I J hstruct a).val := by
    rw [hposA]
    have hdA : (tupleNetworkSource J a).val +
        ((tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val) ≤
        tupleNetworkBound J := by
      rw [Nat.add_sub_of_le hsourceA]
      exact Nat.le_of_lt_succ (tupleNetworkSink I J hstruct a).isLt
    have hle := alphaBlockPosition_le_endpoint
      (tupleNetworkSource J a)
      ((tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val) hdA s
    rw [Nat.add_sub_of_le hsourceA] at hle
    exact hle
  have hgeB :
      (tupleNetworkSource J b).val ≤
        ((alphaTuplePath D I J hstruct b).position s).val := by
    rw [hposB]
    apply alphaBlockPosition_ge_source
  have horder :
      ((alphaTuplePath D I J hstruct a).position s).val <
        ((alphaTuplePath D I J hstruct b).position s).val :=
    hleA.trans_lt (hsep.trans_le hgeB)
  intro hcollision
  change (alphaTuplePath D I J hstruct a).position s =
    (alphaTuplePath D I J hstruct b).position s at hcollision
  have hcollisionVal := congrArg Fin.val hcollision
  exact (Nat.ne_of_lt horder) hcollisionVal

/-- Hook inequalities construct a good reflected path family for one alpha block. -/
theorem exists_tuple_paths_of_indexHook_p_one_q_zero
    {r : ℕ} (D : FiniteEdreiData 1 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 1 0) :
    Nonempty (TupleVertexDisjointPathFamily D I J hstruct) := by
  exact ⟨⟨alphaTupleTerm D I J hstruct,
    alphaTupleTerm_good D I J hstruct hhook⟩⟩

/-- A good reflected path family supplies the intermediate strip partition condition. -/
theorem tuple_paths_nonempty_implies_hasIntermediateStripPartition
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r}
    (hstruct : StructurallyAdmissible I J)
    (hpaths : Nonempty (TupleVertexDisjointPathFamily D I J hstruct)) :
    HasIntermediateStripPartition I J p q := by
  obtain ⟨F⟩ := hpaths
  let M := F.intermediate
  let nu : ℕ → ℕ := fun t ↦ if ht : t < r then M.middle ⟨t, ht⟩ else 0
  have hnu_partition : IsPartitionSequence nu := by
    intro t u htu
    by_cases hu : u < r
    · have ht : t < r := lt_of_le_of_lt htu hu
      simp only [nu, dif_pos ht, dif_pos hu]
      exact M.middle.antitone (Fin.mk_le_mk.mpr (by simpa using htu))
    · simp [nu, hu]
  have hnu_inner : ∀ t, I.associatedPartZeroTail t ≤ nu t := by
    intro t
    by_cases ht : t < r
    · let a : Fin r := ⟨t, ht⟩
      rw [IncreasingIndexTuple.associatedPartZeroTail_apply I ht]
      simp only [nu, dif_pos ht]
      change I.associatedPart a ≤ M.middle a
      exact M.inner_le a
    · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
  have hnu_outer : ∀ t, nu t ≤ J.associatedPartZeroTail t := by
    intro t
    by_cases ht : t < r
    · let a : Fin r := ⟨t, ht⟩
      rw [IncreasingIndexTuple.associatedPartZeroTail_apply J ht]
      simp only [nu, dif_pos ht]
      change M.middle a ≤ J.associatedPart a
      exact M.outer_ge a
    · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
  have hnu_row : ∀ t, J.associatedPartZeroTail t - nu t ≤ q := by
    intro t
    by_cases ht : t < r
    · let a : Fin r := ⟨t, ht⟩
      have hbound := (F.1.2 a).position_le_source_add_stage
        (betaBoundaryVertex p q J.tupleWidth)
      have hperm := tupleNetwork_good_perm_eq_refl F.1 F.2
      change ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val ≤
        (tupleNetworkSource J (F.1.1 a)).val + q at hbound
      have hsourceEq : tupleNetworkSource J (F.1.1 a) = tupleNetworkSource J a := by
        rw [hperm]
        rfl
      rw [congrArg Fin.val hsourceEq] at hbound
      rw [IncreasingIndexTuple.associatedPartZeroTail_apply J ht]
      simp only [nu, dif_pos ht]
      change containingOuterPartition J a -
          reflectedWirePart a ((F.1.2 a).position
            (betaBoundaryVertex p q J.tupleWidth)) ≤ q
      rw [← reflectedWirePart_source J a]
      unfold reflectedWirePart
      omega
    · simp [IncreasingIndexTuple.associatedPartZeroTail, nu, ht]
  have hnu_column : ∀ t, nu (t + p) ≤ I.associatedPartZeroTail t := by
    intro t
    by_cases htp : t + p < r
    · have ht : t < r := by omega
      let a : Fin r := ⟨t, ht⟩
      let b : Fin r := ⟨t + p, htp⟩
      have hchain := F.alphaBoundary_chain a p (by omega) htp
      have hzero : (⟨p - p, Nat.lt_succ_of_le (Nat.sub_le p p)⟩ : Fin (p + 1)) = 0 := by
        apply Fin.ext
        simp
      rw [alphaBoundaryVertex_last, hzero, alphaBoundaryVertex_zero] at hchain
      dsimp [a] at hchain
      rw [IncreasingIndexTuple.associatedPartZeroTail_apply I ht]
      simp only [nu, dif_pos htp]
      change reflectedWirePart (⟨t + p, htp⟩ : Fin r)
          ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
          (betaBoundaryVertex p q J.tupleWidth)) ≤ containedInnerPartition I J hstruct a
      have hrev : (⟨t + p, htp⟩ : Fin r).rev.val + p = a.rev.val := by
        dsimp [a]
        change r - ((t + p) + 1) + p = r - (t + 1)
        omega
      dsimp [a] at hrev
      have hboundA : a.rev.val + (tupleNetworkSink I J hstruct a).val ≤ J.tupleWidth := by
        change a.rev.val + (J.tupleWidth - (I a.rev - 1)) ≤ J.tupleWidth
        have hI := I.position_le a.rev
        have hI' : a.rev.val ≤ I a.rev - 1 := by omega
        have hIwidth : I a.rev ≤ J.tupleWidth :=
          (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        omega
      have hpositionB := (F.1.2 (⟨t + p, htp⟩ : Fin r)).position_le_sink
        (betaBoundaryVertex p q J.tupleWidth)
      change ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
          (betaBoundaryVertex p q J.tupleWidth)).val ≤
        (tupleNetworkSink I J hstruct (⟨t + p, htp⟩ : Fin r)).val at hpositionB
      change ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
          (betaBoundaryVertex p q J.tupleWidth)).val ≤
        J.tupleWidth - (I (⟨t + p, htp⟩ : Fin r).rev - 1) at hpositionB
      have hboundB : (⟨t + p, htp⟩ : Fin r).rev.val +
          ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
            (betaBoundaryVertex p q J.tupleWidth)).val ≤
          J.tupleWidth := by
        change (⟨t + p, htp⟩ : Fin r).rev.val +
          ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
            (betaBoundaryVertex p q J.tupleWidth)).val ≤
          J.tupleWidth
        have hI := I.position_le (⟨t + p, htp⟩ : Fin r).rev
        have hI' : (⟨t + p, htp⟩ : Fin r).rev.val ≤
            I (⟨t + p, htp⟩ : Fin r).rev - 1 := by omega
        have hIwidth : I (⟨t + p, htp⟩ : Fin r).rev ≤ J.tupleWidth :=
          (hstruct (⟨t + p, htp⟩ : Fin r).rev).trans
            (J.value_le_tupleWidth (⟨t + p, htp⟩ : Fin r).rev)
        omega
      dsimp [a] at hboundA
      rw [(F.1.2 a).sink_eq] at hchain
      have hchain' : p + (tupleNetworkSink I J hstruct a).val ≤
          ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
            (betaBoundaryVertex p q J.tupleWidth)).val := by
        change p + (tupleNetworkSink I J hstruct a).val ≤
          ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
            (betaBoundaryVertex p q J.tupleWidth)).val at hchain
        exact hchain
      calc
        reflectedWirePart (⟨t + p, htp⟩ : Fin r)
            ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
            (betaBoundaryVertex p q J.tupleWidth)) ≤
            reflectedWirePart a (tupleNetworkSink I J hstruct a) := by
          unfold reflectedWirePart
          dsimp [a]
          have hsum : (r - (t + 1)) + (tupleNetworkSink I J hstruct
              (⟨t, ht⟩ : Fin r)).val ≤
              (r - (t + p + 1)) +
                ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
                  (betaBoundaryVertex p q J.tupleWidth)).val := by
            calc
              (r - (t + 1)) + (tupleNetworkSink I J hstruct
                  (⟨t, ht⟩ : Fin r)).val =
                  (r - (t + p + 1)) + p +
                    (tupleNetworkSink I J hstruct (⟨t, ht⟩ : Fin r)).val := by
                omega
              _ ≤ (r - (t + p + 1)) +
                    ((F.1.2 (⟨t + p, htp⟩ : Fin r)).position
                      (betaBoundaryVertex p q J.tupleWidth)).val := by
                simpa [Nat.add_assoc] using Nat.add_le_add_left hchain'
                  (r - (t + p + 1))
          exact Nat.sub_le_sub_left hsum J.tupleWidth
        _ = containedInnerPartition I J hstruct a :=
          reflectedWirePart_sink I J hstruct a
    · have hz : nu (t + p) = 0 := by simp [nu, htp]
      rw [hz]
      exact Nat.zero_le _
  exact ⟨nu, hnu_partition, hnu_inner, hnu_outer, hnu_row, hnu_column⟩

/-- The intermediate partition from a good path family gives the finite hook inequalities. -/
theorem tuple_paths_nonempty_implies_indexHookInequalities
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r}
    (hstruct : StructurallyAdmissible I J)
    (hpaths : Nonempty (TupleVertexDisjointPathFamily D I J hstruct)) :
    IndexHookInequalities I J p q := by
  have hstrip := tuple_paths_nonempty_implies_hasIntermediateStripPartition
    hstruct hpaths
  exact partitionHookInequalities_iff_indexHook I J p q |>.mp
    ((hasIntermediateStripPartition_iff_partitionHook I J p q hstruct).mp hstrip)

/-- At gamma zero, positivity of a finite-factor minor forces every support inequality. -/
theorem finiteFactorMinor_pos_implies_indexHook_of_gamma_zero
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r)
    (hpos : 0 < FiniteEdreiData.finiteFactorMinor D I J) :
    StructurallyAdmissible I J ∧ IndexHookInequalities I J p q := by
  have hstruct := FiniteEdreiData.structurallyAdmissible_of_finiteFactorMinor_pos D I J hpos
  have hpaths := (finiteFactorMinor_pos_iff_nonempty_tuple_paths D hgamma I J hstruct).mp hpos
  exact ⟨hstruct, tuple_paths_nonempty_implies_indexHookInequalities hstruct hpaths⟩

/-- Hook inequalities construct a good reflected path family in the beta-only case. -/
theorem exists_tuple_paths_of_indexHook_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J)
    (hhook : IndexHookInequalities I J 0 q) :
    Nonempty (TupleVertexDisjointPathFamily D I J hstruct) := by
  exact ⟨⟨betaTupleTerm D I J hstruct hhook,
    betaTupleTerm_good D I J hstruct hhook⟩⟩

/-- In the beta-only case, nonemptiness of the reflected path family is exactly the hook condition.
-/
theorem tuple_paths_nonempty_iff_indexHook_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Nonempty (TupleVertexDisjointPathFamily D I J hstruct) ↔
      IndexHookInequalities I J 0 q := by
  constructor
  · exact tuple_paths_nonempty_implies_indexHookInequalities hstruct
  · exact exists_tuple_paths_of_indexHook_p_zero D I J hstruct

/-- The gamma-zero finite-factor support theorem is unconditional when there are no alpha factors.
-/
theorem finiteFactorMinor_pos_iff_indexHook_p_zero
    {q r : ℕ} (D : FiniteEdreiData 0 q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J 0 q := by
  constructor
  · exact finiteFactorMinor_pos_implies_indexHook_of_gamma_zero D hgamma I J
  · rintro ⟨hstruct, hhook⟩
    apply (finiteFactorMinor_pos_iff_nonempty_tuple_paths D hgamma I J hstruct).mpr
    exact exists_tuple_paths_of_indexHook_p_zero D I J hstruct hhook

/-- The gamma-zero finite-factor support theorem for one alpha block and no beta factors. -/
theorem finiteFactorMinor_pos_iff_indexHook_p_one_q_zero
    {r : ℕ} (D : FiniteEdreiData 1 0) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J 1 0 := by
  constructor
  · exact finiteFactorMinor_pos_implies_indexHook_of_gamma_zero D hgamma I J
  · rintro ⟨hstruct, hhook⟩
    apply (finiteFactorMinor_pos_iff_nonempty_tuple_paths D hgamma I J hstruct).mpr
    exact exists_tuple_paths_of_indexHook_p_one_q_zero D I J hstruct hhook

/-- A good reflected path family forces the concrete tableau family to be nonempty.  This is the
non-weighted half of the path/tableau correspondence for arbitrary `p,q`. -/
theorem tuple_paths_nonempty_implies_nonempty_tupleCoproduct
    {p q r : ℕ} (D : FiniteEdreiData p q) (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (hpaths : Nonempty (TupleVertexDisjointPathFamily D I J hstruct)) :
    Nonempty (TupleCoproductTableau (p := p) (q := q) I J hstruct) := by
  have hhook := tuple_paths_nonempty_implies_indexHookInequalities hstruct hpaths
  exact (tupleCoproduct_nonempty_iff_indexHook I J hstruct).mpr hhook

end

end ToeplitzPositroids.Edrei
