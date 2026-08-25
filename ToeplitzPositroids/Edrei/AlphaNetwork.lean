import ToeplitzPositroids.Edrei.FiniteFactorNetworkConcrete

/-!
# Explicit paths through one alpha block

An alpha block consists of adjacent chips visited from wire `0` to wire `N`.  A path that starts at
`x` and makes `d` moves therefore moves at the consecutive stages `x, ..., x+d-1`.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- The canonical position at a vertex of one alpha block. -/
def alphaBlockPosition {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (s : Fin (finiteFactorStageCount 1 0 N + 1)) : Fin (N + 1) :=
  ⟨source.val + if source.val ≤ s.val then min d (s.val - source.val) else 0, by
    by_cases hsource : source.val ≤ s.val
    · have hmin : min d (s.val - source.val) ≤ d := Nat.min_le_left _ _
      rw [if_pos hsource]
      exact Nat.lt_succ_of_le ((Nat.add_le_add_left hmin source.val).trans hd)
    · rw [if_neg hsource]
      exact source.isLt⟩

theorem alphaBlockPosition_ge_source {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (s : Fin (finiteFactorStageCount 1 0 N + 1)) :
    source.val ≤ (alphaBlockPosition source d hd s).val := by
  unfold alphaBlockPosition
  split_ifs
  · change source.val ≤ source.val + min d (s.val - source.val)
    exact Nat.le_add_right _ _
  · rfl

theorem alphaBlockPosition_le_endpoint {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (s : Fin (finiteFactorStageCount 1 0 N + 1)) :
    (alphaBlockPosition source d hd s).val ≤ source.val + d := by
  unfold alphaBlockPosition
  split_ifs
  · exact Nat.add_le_add_left (Nat.min_le_left _ _) _
  · simp

theorem alphaBlockPosition_step {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (t : Fin (finiteFactorStageCount 1 0 N)) :
    (alphaBlockPosition source d hd t.succ).val =
        (alphaBlockPosition source d hd t.castSucc).val ∨
      (alphaBlockPosition source d hd t.succ).val =
        (alphaBlockPosition source d hd t.castSucc).val + 1 := by
  have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
  by_cases hsource : source.val ≤ t.val
  · by_cases hdone : d ≤ t.val - source.val
    · left
      dsimp [alphaBlockPosition]
      have hnextsource : source.val ≤ t.val + 1 := by omega
      have hminNext : min d (t.val + 1 - source.val) = d :=
        Nat.min_eq_left (by omega)
      simp [hsource, hnextsource, Nat.min_eq_left hdone, hminNext]
    · right
      have hbefore : t.val - source.val < d := Nat.lt_of_not_ge hdone
      have hcurrent : source.val + min d (t.val - source.val) = t.val := by
        rw [Nat.min_eq_right (Nat.le_of_lt hbefore)]
        omega
      have hnext : source.val + min d (t.val + 1 - source.val) = t.val + 1 := by
        have hnextsource : source.val ≤ t.val + 1 := by omega
        rw [Nat.min_eq_right (by omega : t.val + 1 - source.val ≤ d)]
        omega
      have hnextsource : source.val ≤ t.val + 1 := by omega
      dsimp [alphaBlockPosition]
      rw [if_pos hsource, if_pos hnextsource]
      omega
  · left
    dsimp [alphaBlockPosition]
    by_cases hnext : source.val ≤ t.val + 1
    · have heq : source.val = t.val + 1 := by omega
      simp [heq]
    · simp [hsource, hnext]

/-- A path through a single alpha block with an arbitrary admissible displacement. -/
noncomputable def alphaBlockPath {N : ℕ} (D : FiniteEdreiData 1 0)
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val) :
    FiniteFactorPath D N source sink := by
  let d := sink.val - source.val
  have hsum : source.val + d = sink.val := Nat.add_sub_of_le hsource
  have hsink : source.val + d ≤ N := by
    rw [hsum]
    exact Nat.le_of_lt_succ sink.isLt
  let f : Fin (finiteFactorStageCount 1 0 N + 1) → Fin (N + 1) :=
    alphaBlockPosition source d hsink
  have hfzero : f 0 = source := by
    apply Fin.ext
    dsimp [f, alphaBlockPosition]
    by_cases hsource : source.val = 0
    · simp [hsource]
    · have hnot : ¬source.val ≤ 0 := by omega
      simp [hnot]
  have hflast : f (Fin.last (finiteFactorStageCount 1 0 N)) = sink := by
    apply Fin.ext
    dsimp [f, alphaBlockPosition]
    have hstage : finiteFactorStageCount 1 0 N = N := by
      simp [finiteFactorStageCount]
    rw [hstage]
    change (source.val + (if source.val ≤ N then min d (N - source.val) else 0)) = sink.val
    have hsourceN : source.val ≤ N := Nat.le_of_lt_succ source.isLt
    have hmin : min d (N - source.val) = d := Nat.min_eq_left (by omega)
    simp only [if_pos hsourceN, hmin]
    exact hsum
  refine { position := f, source_eq := hfzero, sink_eq := ?_, valid := ?_ }
  · simpa [finiteFactorStageCount] using hflast
  · intro t
    have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
    unfold NetworkStepAllowed
    rw [if_neg (by omega : ¬t.val < 0)]
    let x := source.val
    let d' := d
    by_cases hsource_t : x ≤ t.val
    · by_cases hdone : d' ≤ t.val - x
      · left
        have hsource_t' : source.val ≤ t.val := by simpa [x] using hsource_t
        have hdone' : d ≤ t.val - source.val := by simpa [d'] using hdone
        dsimp [f, alphaBlockPosition, x, d']
        have hnextsource : source.val ≤ t.val + 1 := by omega
        have hminNext : min d (t.val + 1 - source.val) = d :=
          Nat.min_eq_left (by omega)
        simp [hsource_t', hnextsource, Nat.min_eq_left hdone', hminNext]
      · right
        have hbefore : t.val - x < d' := Nat.lt_of_not_ge hdone
        have hnext : x + min d' (t.val + 1 - x) = t.val + 1 := by
          have hxt : x ≤ t.val + 1 := by omega
          have hmin : min d' (t.val + 1 - x) = t.val + 1 - x :=
            Nat.min_eq_right (by omega)
          simp only [hmin]
          omega
        have hcurrent : x + min d' (t.val - x) = t.val := by
          have hmin : min d' (t.val - x) = t.val - x :=
            Nat.min_eq_right (by omega)
          simp only [hmin]
          omega
        dsimp [f, alphaBlockPosition, x, d']
        have hsource_t' : source.val ≤ t.val := by simpa [x] using hsource_t
        have hcurrent' : source.val + min d (t.val - source.val) = t.val := by
          simpa [x, d'] using hcurrent
        have hnext' : source.val + min d (t.val + 1 - source.val) = t.val + 1 := by
          simpa [x, d'] using hnext
        have hN : 0 < N := by
          by_contra hN
          have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
          subst N
          have ht0 := t.isLt
          simp [finiteFactorStageCount] at ht0
        have hdiv : t.val / N = 0 := Nat.div_eq_of_lt ht
        have hmod : t.val % N = t.val := Nat.mod_eq_of_lt ht
        have hsource_next : source.val ≤ t.val + 1 := by omega
        simp [hsource_t', hsource_next, hcurrent', hnext', hdiv, hmod]
    · left
      have hsource_t' : ¬source.val ≤ t.val := by simpa [x] using hsource_t
      dsimp [f, alphaBlockPosition, x, d']
      by_cases hnext : source.val ≤ t.val + 1
      · have heq : source.val = t.val + 1 := by omega
        simp [heq]
      · simp [hsource_t', hnext]

@[simp]
theorem alphaBlockPath_position {N : ℕ} (D : FiniteEdreiData 1 0)
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (s : Fin (finiteFactorStageCount 1 0 N + 1)) :
    (alphaBlockPath D hsource).position s =
      alphaBlockPosition source (sink.val - source.val)
        (by
          rw [Nat.add_sub_of_le hsource]
          exact Nat.le_of_lt_succ sink.isLt) s := by
  rfl

theorem alphaPath_stepWeight_eq_if_move
    {N : ℕ} {D : FiniteEdreiData 1 0}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount 1 0 N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        (P.position t.castSucc) (P.position t.succ) =
      if (P.position t.succ).val = (P.position t.castSucc).val then 1
      else D.alpha 0 := by
  have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
  have hv := P.valid t
  unfold NetworkStepAllowed at hv
  rw [if_neg (by omega : ¬t.val < 0)] at hv
  unfold FiniteEdreiData.networkStepWeight
  by_cases hstay : (P.position t.succ).val = (P.position t.castSucc).val
  · simp [hstay]
  · rw [if_neg hstay]
    rcases hv with hv | hv
    · exact False.elim (hstay hv)
    · have hN : 0 < N := by
        by_contra hN
        have hN0 : N = 0 := Nat.eq_zero_of_not_pos hN
        subst N
        simp [finiteFactorStageCount] at ht
      have hdiv : t.val / N = 0 := Nat.div_eq_of_lt ht
      have hidx : (⟨t.val / N, hv.1⟩ : Fin 1) = 0 := by
        apply Fin.ext
        simp [hdiv]
      simp [ht, hv, hidx]

theorem alphaBlockPath_stepWeight_eq_if_interval
    {N : ℕ} {D : FiniteEdreiData 1 0}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (t : Fin (finiteFactorStageCount 1 0 N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        ((alphaBlockPath D hsource).position t.castSucc)
        ((alphaBlockPath D hsource).position t.succ) =
      if source.val ≤ t.val ∧ t.val < sink.val then D.alpha 0 else 1 := by
  have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
  rw [alphaPath_stepWeight_eq_if_move]
  rw [alphaBlockPath_position, alphaBlockPath_position]
  let d := sink.val - source.val
  have hsum : source.val + d = sink.val := by
    dsimp [d]
    exact Nat.add_sub_of_le hsource
  have hd : source.val + d ≤ N := by
    rw [hsum]
    exact Nat.le_of_lt_succ sink.isLt
  by_cases hinter : source.val ≤ t.val ∧ t.val < sink.val
  · have hst : source.val ≤ t.val := hinter.1
    have hts : t.val - source.val < d := by omega
    have hnextsource : source.val ≤ t.val + 1 := by omega
    have hcurrent : source.val + min d (t.val - source.val) = t.val := by
      rw [Nat.min_eq_right (Nat.le_of_lt hts)]
      omega
    have hnext : source.val + min d (t.val + 1 - source.val) = t.val + 1 := by
      rw [Nat.min_eq_right (by omega : t.val + 1 - source.val ≤ d)]
      omega
    have hcurrent' :
        (alphaBlockPosition source (sink.val - source.val)
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val = t.val := by
      dsimp [alphaBlockPosition]
      simp only [if_pos hst]
      simpa [d] using hcurrent
    have hnext' :
        (alphaBlockPosition source (sink.val - source.val)
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.succ).val = t.val + 1 := by
      dsimp [alphaBlockPosition]
      simp only [if_pos hnextsource]
      simpa [d] using hnext
    have hneq : ¬
        (alphaBlockPosition source (sink.val - source.val)
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.succ).val =
        (alphaBlockPosition source (sink.val - source.val)
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
      rw [hcurrent', hnext']
      omega
    simp [hneq, hinter]
  · rw [if_neg hinter]
    by_cases hbefore : t.val < source.val
    · have hbefore_next : t.val + 1 < source.val ∨ t.val + 1 = source.val := by omega
      rcases hbefore_next with hnext | hnext
      · have hnot : ¬source.val ≤ t.val := by omega
        have hnotnext : ¬source.val ≤ t.val + 1 := by omega
        have hcurrent' :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val = source.val := by
          dsimp [alphaBlockPosition]
          simp [hnot]
        have hnext' :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.succ).val = source.val := by
          dsimp [alphaBlockPosition]
          simp [hnotnext]
        have heqPos :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.succ).val =
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
          rw [hcurrent', hnext']
        simp [heqPos]
      · have hnot : ¬source.val ≤ t.val := by omega
        have heq : source.val = t.val + 1 := hnext.symm
        have hcurrent' :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val = source.val := by
          dsimp [alphaBlockPosition]
          simp [hnot]
        have hnext' :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.succ).val = source.val := by
          dsimp [alphaBlockPosition]
          simp [heq]
        have heqPos :
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.succ).val =
            (alphaBlockPosition source (sink.val - source.val)
              (by
                rw [Nat.add_sub_of_le hsource]
                exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
          rw [hcurrent', hnext']
        simp [heqPos]
    · have hsource_t : source.val ≤ t.val := by omega
      have hafter : sink.val ≤ t.val := by omega
      have hdone : d ≤ t.val - source.val := by omega
      have hdone_next : d ≤ t.val + 1 - source.val := by omega
      have hmin : min d (t.val - source.val) = d := Nat.min_eq_left hdone
      have hmin_next : min d (t.val + 1 - source.val) = d :=
        Nat.min_eq_left hdone_next
      have hcurrent' :
          (alphaBlockPosition source (sink.val - source.val)
            (by
              rw [Nat.add_sub_of_le hsource]
              exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val = sink.val := by
        dsimp [alphaBlockPosition]
        rw [if_pos hsource_t, Nat.min_eq_left hdone]
        omega
      have hnext' :
          (alphaBlockPosition source (sink.val - source.val)
            (by
              rw [Nat.add_sub_of_le hsource]
              exact Nat.le_of_lt_succ sink.isLt) t.succ).val = sink.val := by
        dsimp [alphaBlockPosition]
        rw [if_pos (by omega : source.val ≤ t.val + 1),
          Nat.min_eq_left hdone_next]
        omega
      have heqPos :
          (alphaBlockPosition source (sink.val - source.val)
            (by
              rw [Nat.add_sub_of_le hsource]
              exact Nat.le_of_lt_succ sink.isLt) t.succ).val =
          (alphaBlockPosition source (sink.val - source.val)
            (by
              rw [Nat.add_sub_of_le hsource]
              exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
        rw [hcurrent', hnext']
      simp [heqPos]

theorem alphaBlockPath_weight_eq_interval_product
    {N : ℕ} {D : FiniteEdreiData 1 0}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val) :
    (alphaBlockPath D hsource).weight =
      ∏ t : Fin (finiteFactorStageCount 1 0 N),
        (if source.val ≤ t.val ∧ t.val < sink.val then D.alpha 0 else 1) := by
  unfold FiniteFactorPath.weight
  refine Finset.prod_congr rfl ?_
  intro t _
  exact alphaBlockPath_stepWeight_eq_if_interval (D := D) hsource t

end

end ToeplitzPositroids.Edrei
