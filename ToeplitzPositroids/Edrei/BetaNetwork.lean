import ToeplitzPositroids.Edrei.FiniteFactorNetworkConcrete

/-!
# Explicit beta-block paths

This file records the elementary path construction through the finite beta block.  It is a
local ingredient of the fully formalized zero-gamma network/tableau bridge.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- The canonical position function that makes all possible beta moves as early as possible. -/
def betaFactorPosition {q N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (s : Fin (finiteFactorStageCount 0 q N + 1)) : Fin (N + 1) :=
  ⟨source.val + min d s.val, by
    have hmin : min d s.val ≤ d := Nat.min_le_left _ _
    omega⟩

/-- A canonical path through a beta-only block, with its moves taken at the first available chips.
The endpoint hypotheses are explicit so that the position formula is available for later family
constructions.
-/
noncomputable def betaFactorPath {q N : ℕ} (D : FiniteEdreiData 0 q)
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (hdisplacement : sink.val - source.val ≤ q) :
    FiniteFactorPath D N source sink := by
  let d := sink.val - source.val
  have hstage : finiteFactorStageCount 0 q N = q := by
    simp [finiteFactorStageCount]
  have hsum : source.val + d = sink.val := Nat.add_sub_of_le hsource
  have hd : d ≤ q := hdisplacement
  have hsink : source.val + d ≤ N := by
    rw [hsum]
    exact Nat.le_of_lt_succ sink.isLt
  let f : Fin (finiteFactorStageCount 0 q N + 1) → Fin (N + 1) :=
    betaFactorPosition source d hsink
  have hfzero : f 0 = source := by
    apply Fin.ext
    dsimp [f, betaFactorPosition]
    simp
  have hflast : f (Fin.last (finiteFactorStageCount 0 q N)) = sink := by
    apply Fin.ext
    dsimp [f, betaFactorPosition]
    rw [hstage]
    rw [Nat.min_eq_left hd]
    exact hsum
  refine { position := f, source_eq := hfzero, sink_eq := ?_, valid := ?_ }
  · simpa [finiteFactorStageCount] using hflast
  · intro t
    have ht : t.val < q := by simpa [hstage] using t.isLt
    have hmin : min d (t.val + 1) = min d t.val ∨
        min d (t.val + 1) = min d t.val + 1 := by
      by_cases hdt : d ≤ t.val
      · left
        rw [Nat.min_eq_left hdt, Nat.min_eq_left (hdt.trans (Nat.le_succ _))]
      · right
        have htd : t.val < d := Nat.lt_of_not_ge hdt
        by_cases hdt1 : d ≤ t.val + 1
        · have heq : d = t.val + 1 := by omega
          simp [heq]
        · have hle : t.val + 1 ≤ d := by omega
          rw [Nat.min_eq_right hle, Nat.min_eq_right (Nat.le_of_lt htd)]
    unfold NetworkStepAllowed
    rw [if_pos ht]
    rcases hmin with hstay | hmove
    · left
      dsimp [f, betaFactorPosition] at hstay ⊢
      omega
    · right
      dsimp [f, betaFactorPosition] at hmove ⊢
      omega

@[simp]
theorem betaFactorPath_position {q N : ℕ} (D : FiniteEdreiData 0 q)
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (hdisplacement : sink.val - source.val ≤ q)
    (s : Fin (finiteFactorStageCount 0 q N + 1)) :
    (betaFactorPath D hsource hdisplacement).position s =
      betaFactorPosition source (sink.val - source.val)
        (by
          rw [Nat.add_sub_of_le hsource]
          exact Nat.le_of_lt_succ sink.isLt) s := by
  rfl

theorem betaPath_stepWeight_eq_if_move
    {q N : ℕ} {D : FiniteEdreiData 0 q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount 0 q N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        (P.position t.castSucc) (P.position t.succ) =
      if (P.position t.succ).val = (P.position t.castSucc).val then 1
      else D.beta ⟨t.val, by simpa [finiteFactorStageCount] using t.isLt⟩ := by
  have ht : t.val < q := by simpa [finiteFactorStageCount] using t.isLt
  have hv := P.valid t
  unfold NetworkStepAllowed at hv
  rw [if_pos ht] at hv
  unfold FiniteEdreiData.networkStepWeight
  by_cases hstay : (P.position t.succ).val = (P.position t.castSucc).val
  · simp [hstay]
  · rw [if_neg hstay]
    rcases hv with hv | hv
    · exact False.elim (hstay hv)
    · simp [ht, hv]

theorem betaPath_weight_eq_prod_if_move
    {q N : ℕ} {D : FiniteEdreiData 0 q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    P.weight =
      ∏ t : Fin (finiteFactorStageCount 0 q N),
        (if (P.position t.succ).val = (P.position t.castSucc).val then 1
         else D.beta ⟨t.val, by simpa [finiteFactorStageCount] using t.isLt⟩) := by
  unfold FiniteFactorPath.weight
  apply Finset.prod_congr rfl
  intro t _
  exact betaPath_stepWeight_eq_if_move P t

theorem betaFactorPath_stepWeight_eq_if_before
    {q N : ℕ} {D : FiniteEdreiData 0 q}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (hdisplacement : sink.val - source.val ≤ q)
    (t : Fin (finiteFactorStageCount 0 q N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        ((betaFactorPath D hsource hdisplacement).position t.castSucc)
        ((betaFactorPath D hsource hdisplacement).position t.succ) =
      if t.val < sink.val - source.val then
        D.beta ⟨t.val, by simpa [finiteFactorStageCount] using t.isLt⟩
      else 1 := by
  rw [betaPath_stepWeight_eq_if_move]
  rw [betaFactorPath_position, betaFactorPath_position]
  let d := sink.val - source.val
  by_cases hmove : t.val < d
  · have hmin : min d t.val = t.val := Nat.min_eq_right (Nat.le_of_lt hmove)
    have hmin_next : min d (t.val + 1) = t.val + 1 :=
      Nat.min_eq_right (by omega)
    have hneq :
        (betaFactorPosition source d
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.succ).val ≠
        (betaFactorPosition source d
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
      dsimp [betaFactorPosition]
      rw [hmin, hmin_next]
      omega
    simp [d, hmove, hneq]
  · have hdone : d ≤ t.val := Nat.le_of_not_gt hmove
    have hdone_next : d ≤ t.val + 1 := hdone.trans (Nat.le_succ _)
    have heq :
        (betaFactorPosition source d
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.succ).val =
        (betaFactorPosition source d
          (by
            rw [Nat.add_sub_of_le hsource]
            exact Nat.le_of_lt_succ sink.isLt) t.castSucc).val := by
      dsimp [betaFactorPosition]
      rw [Nat.min_eq_left hdone, Nat.min_eq_left hdone_next]
    simp [d, hmove, heq]

theorem betaFactorPath_weight_eq_before_product
    {q N : ℕ} {D : FiniteEdreiData 0 q}
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (hdisplacement : sink.val - source.val ≤ q) :
    (betaFactorPath D hsource hdisplacement).weight =
      ∏ t : Fin (finiteFactorStageCount 0 q N),
        (if t.val < sink.val - source.val then
          D.beta ⟨t.val, by simpa [finiteFactorStageCount] using t.isLt⟩
         else 1) := by
  unfold FiniteFactorPath.weight
  refine Finset.prod_congr rfl ?_
  intro t _
  exact betaFactorPath_stepWeight_eq_if_before
    (D := D) hsource hdisplacement t

/-- A beta block contains a path between any weakly ordered endpoints whose displacement is at
most the number of beta chips. -/
theorem exists_beta_factor_path {q N : ℕ} (D : FiniteEdreiData 0 q)
    {source sink : Fin (N + 1)} (hsource : source.val ≤ sink.val)
    (hdisplacement : sink.val - source.val ≤ q) :
    Nonempty (FiniteFactorPath (p := 0) D N source sink) := by
  exact ⟨betaFactorPath D hsource hdisplacement⟩

end

end ToeplitzPositroids.Edrei
