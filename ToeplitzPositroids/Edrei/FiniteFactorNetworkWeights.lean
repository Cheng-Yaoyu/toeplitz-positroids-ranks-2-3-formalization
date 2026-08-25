import ToeplitzPositroids.Edrei.FiniteFactorNetwork

/-!
# Uniform local weight formula for finite-factor paths

The network has only two kinds of valid edges: a horizontal edge of weight one and a single
upward edge at the chip currently being visited.  This file records that fact in a form that is
independent of the particular path construction used later.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

theorem FiniteFactorPath.stepWeight_eq_if_move_parameter
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount p q N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        (P.position t.castSucc) (P.position t.succ) =
      if _hstay : (P.position t.succ).val = (P.position t.castSucc).val then 1
      else if ht : t.val < q then D.beta ⟨t.val, ht⟩
      else if ha : (t.val - q) / N < p then
        D.alpha ⟨(t.val - q) / N, ha⟩
      else 0 := by
  have hv := P.valid t
  unfold NetworkStepAllowed at hv
  unfold FiniteEdreiData.networkStepWeight
  by_cases hstay : (P.position t.succ).val = (P.position t.castSucc).val
  · simp [hstay]
  · simp only [if_neg hstay]
    by_cases ht : t.val < q
    · simp only [dif_pos ht]
      have hvalid :
          (P.position t.succ).val = (P.position t.castSucc).val + 1 := by
        rw [if_pos ht] at hv
        rcases hv with hsame | hmove
        · exact False.elim (hstay hsame)
        · exact hmove
      simp [hvalid]
    · simp only [dif_neg ht]
      have hvalid := hv
      rw [if_neg ht] at hvalid
      let u := t.val - q
      by_cases ha : u / N < p
      · dsimp [u] at ha ⊢
        simp only [dif_pos ha]
        have hpair :
            (P.position t.castSucc).val = u % N ∧
              (P.position t.succ).val = (P.position t.castSucc).val + 1 := by
          rcases hvalid with hsame | hmove
          · exact False.elim (hstay hsame)
          · rcases hmove with ⟨-, hx, hy⟩
            exact ⟨by simpa [u] using hx, hy⟩
        simp [hpair, u]
      · dsimp [u] at ha ⊢
        simp only [dif_neg ha]
        rcases hvalid with hsame | hmove
        · exact False.elim (hstay hsame)
        · exact False.elim (ha hmove.1)

theorem FiniteFactorPath.weight_eq_prod_if_move_parameter
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    P.weight =
      ∏ t : Fin (finiteFactorStageCount p q N),
        (if _hstay : (P.position t.succ).val = (P.position t.castSucc).val then 1
         else if ht : t.val < q then D.beta ⟨t.val, ht⟩
         else if ha : (t.val - q) / N < p then
           D.alpha ⟨(t.val - q) / N, ha⟩
         else 0) := by
  unfold FiniteFactorPath.weight
  refine Finset.prod_congr rfl ?_
  intro t _
  exact P.stepWeight_eq_if_move_parameter t

end ToeplitzPositroids.Edrei
