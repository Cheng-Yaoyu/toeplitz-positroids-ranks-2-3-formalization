import ToeplitzPositroids.Edrei.TableauAlphaSplice

/-!
# The mixed beta/alpha splice

This module develops the mixed construction, where beta stages are followed by alpha stages at the
intermediate partition, and proves the global path-family inverse and gamma-zero consequences.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

theorem tupleCoproductTableau_beta_row_bound
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    (tupleNetworkSource J a).val + T.intermediate.betaShape.rowWidth a ≤ J.tupleWidth := by
  rw [FiniteSkewShape.rowWidth_eq_sub]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - T.intermediate.middle a) ≤ J.tupleWidth
  have hmid : T.intermediate.middle a ≤ J.associatedPart a := T.intermediate.outer_ge a
  have hJ := J.value_le_tupleWidth a.rev
  have hJpos := J.position_le a.rev
  change (J.tupleWidth - (J a.rev - 1)) +
      (J a.rev - (a.rev.val + 1) - T.intermediate.middle a) ≤ J.tupleWidth
  omega

theorem tupleCoproductTableau_alpha_row_bound
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    (tupleNetworkSource J a).val + T.intermediate.alphaShape.rowWidth a ≤ J.tupleWidth := by
  rw [FiniteSkewShape.rowWidth_eq_sub]
  change (J.tupleWidth - (J a.rev - 1)) +
      (T.intermediate.middle a - I.associatedPart a) ≤ J.tupleWidth
  have hmid : I.associatedPart a ≤ T.intermediate.middle a := T.intermediate.inner_le a
  have houter : T.intermediate.middle a ≤ J.associatedPart a := T.intermediate.outer_ge a
  have hI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  have hJ := J.value_le_tupleWidth a.rev
  have hIpos := I.position_le a.rev
  have hJpos := J.position_le a.rev
  have hassocI : I.associatedPart a = I a.rev - (a.rev.val + 1) := rfl
  rw [hassocI] at hmid
  change (J.tupleWidth - (J a.rev - 1)) +
      (T.intermediate.middle a - (I a.rev - (a.rev.val + 1))) ≤ J.tupleWidth
  have hsourceOuter : (J.tupleWidth - (J a.rev - 1)) + J.associatedPart a ≤
      J.tupleWidth := by
    change (J.tupleWidth - (J a.rev - 1)) +
        (J a.rev - (a.rev.val + 1)) ≤ J.tupleWidth
    omega
  have hmiddleSub : T.intermediate.middle a - I.associatedPart a ≤ J.associatedPart a :=
    (Nat.sub_le _ _).trans houter
  omega

theorem tupleCoproductTableau_total_row_bound
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    (tupleNetworkSource J a).val +
        T.intermediate.betaShape.rowWidth a +
        T.intermediate.alphaShape.rowWidth a ≤ J.tupleWidth := by
  rw [FiniteSkewShape.rowWidth_eq_sub, FiniteSkewShape.rowWidth_eq_sub]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - T.intermediate.middle a) +
      (T.intermediate.middle a - I.associatedPart a) ≤ J.tupleWidth
  have hinner : I.associatedPart a ≤ T.intermediate.middle a := T.intermediate.inner_le a
  have houter : T.intermediate.middle a ≤ J.associatedPart a := T.intermediate.outer_ge a
  have hJ := J.value_le_tupleWidth a.rev
  have hI := (hstruct a.rev).trans hJ
  have hJpos := J.position_le a.rev
  have hIpos := I.position_le a.rev
  have hcollapse : J.associatedPart a - T.intermediate.middle a +
      (T.intermediate.middle a - I.associatedPart a) =
      J.associatedPart a - I.associatedPart a := by omega
  rw [Nat.add_assoc, hcollapse]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J a.rev - (a.rev.val + 1) - (I a.rev - (a.rev.val + 1))) ≤ J.tupleWidth
  omega

def mixedTableauBoundary
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    Fin (J.tupleWidth + 1) :=
  ⟨(tupleNetworkSource J a).val + T.intermediate.betaShape.rowWidth a, by
    have h := tupleCoproductTableau_beta_row_bound T a
    omega⟩

@[simp] theorem mixedTableauBoundary_val
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    (mixedTableauBoundary T a).val =
      (tupleNetworkSource J a).val + T.intermediate.betaShape.rowWidth a :=
  rfl

theorem mixedTableauBoundary_alpha_bound
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct) (a : Fin r) :
    (mixedTableauBoundary T a).val + T.intermediate.alphaShape.rowWidth a ≤ J.tupleWidth := by
  rw [mixedTableauBoundary_val, FiniteSkewShape.rowWidth_eq_sub,
    FiniteSkewShape.rowWidth_eq_sub]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - T.intermediate.middle a) +
      (T.intermediate.middle a - I.associatedPart a) ≤ J.tupleWidth
  have hinner : I.associatedPart a ≤ T.intermediate.middle a := T.intermediate.inner_le a
  have houter : T.intermediate.middle a ≤ J.associatedPart a := T.intermediate.outer_ge a
  have hJ := J.value_le_tupleWidth a.rev
  have hI := (hstruct a.rev).trans hJ
  have hJpos := J.position_le a.rev
  have hIpos := I.position_le a.rev
  have hcollapse : J.associatedPart a - T.intermediate.middle a +
      (T.intermediate.middle a - I.associatedPart a) =
      J.associatedPart a - I.associatedPart a := by omega
  rw [Nat.add_assoc, hcollapse]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J a.rev - (a.rev.val + 1) - (I a.rev - (a.rev.val + 1))) ≤ J.tupleWidth
  omega

def mixedTableauPosition
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (s : Fin (finiteFactorStageCount p q J.tupleWidth + 1)) :
    Fin (J.tupleWidth + 1) := by
  let boundary := mixedTableauBoundary T a
  let hbetaBound :
      (tupleNetworkSource J a).val + T.intermediate.betaShape.rowWidth a ≤ J.tupleWidth :=
    tupleCoproductTableau_beta_row_bound T a
  let halphaBound :
      boundary.val + T.intermediate.alphaShape.rowWidth a ≤ J.tupleWidth := by
    exact mixedTableauBoundary_alpha_bound T a
  by_cases hs : s.val ≤ q
  · exact betaTableauPosition T.tableaux.betaTableau a (tupleNetworkSource J a)
      hbetaBound ⟨s.val, by
        have hslt := s.isLt
        simp only [finiteFactorStageCount] at hslt ⊢
        omega⟩
  · exact alphaTableauPosition T.tableaux.alphaTableau a boundary halphaBound
      ⟨s.val - q, by
        have hslt := s.isLt
        simp only [finiteFactorStageCount] at hslt ⊢
        omega⟩

@[simp] theorem mixedTableauPosition_of_le_boundary
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (s : Fin (finiteFactorStageCount p q J.tupleWidth + 1))
    (hs : s.val ≤ q) :
    mixedTableauPosition T hp a s =
      betaTableauPosition T.tableaux.betaTableau a (tupleNetworkSource J a)
        (tupleCoproductTableau_beta_row_bound T a) ⟨s.val, by
          have hslt := s.isLt
          simp only [finiteFactorStageCount] at hslt ⊢
          omega⟩ := by
  unfold mixedTableauPosition
  simp only [hs, ↓reduceDIte]

theorem mixedTableauPosition_of_after_boundary
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (s : Fin (finiteFactorStageCount p q J.tupleWidth + 1))
    (hs : q < s.val) :
    mixedTableauPosition T hp a s =
      alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
        (mixedTableauBoundary_alpha_bound T a) ⟨s.val - q, by
          have hslt := s.isLt
          simp only [finiteFactorStageCount] at hslt ⊢
          omega⟩ := by
  unfold mixedTableauPosition
  simp only [not_le.mpr hs, ↓reduceDIte]

theorem mixedTableauPosition_at_boundary
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (a : Fin r) :
    mixedTableauPosition T hp a (betaBoundaryVertex p q J.tupleWidth) =
      mixedTableauBoundary T a := by
  have hbeta := betaTableauPosition_last T.tableaux.betaTableau a
    (tupleNetworkSource J a) (tupleCoproductTableau_beta_row_bound T a)
  rw [mixedTableauPosition_of_le_boundary T hp a _ (by simp [betaBoundaryVertex])]
  apply Fin.ext
  simpa [mixedTableauBoundary, betaBoundaryVertex, finiteFactorStageCount] using
    congrArg Fin.val hbeta

set_option maxHeartbeats 1000000 in
-- The boundary case transports dependent beta and alpha positions to one common vertex.
theorem mixedTableauPosition_network_step
    {p q r : ℕ}
    {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (t : Fin (finiteFactorStageCount p q J.tupleWidth)) :
    NetworkStepAllowed p q J.tupleWidth t.val
      (mixedTableauPosition T hp a t.castSucc)
      (mixedTableauPosition T hp a t.succ) := by
  by_cases ht : t.val < q
  · have hleft := mixedTableauPosition_of_le_boundary T hp a t.castSucc (by
      change t.val ≤ q
      omega)
    have hright := mixedTableauPosition_of_le_boundary T hp a t.succ (by
      change t.val + 1 ≤ q
      omega)
    let u : Fin q := ⟨t.val, ht⟩
    have hstep := betaRowMoveCount_step T.tableaux.betaTableau a u
    unfold NetworkStepAllowed
    rw [if_pos ht]
    rw [hleft, hright]
    rcases hstep with hstay | hmove
    · left
      dsimp [betaTableauPosition]
      have hstay' : betaRowMoveCount T.tableaux.betaTableau a
          ⟨t.val + 1, by omega⟩ = betaRowMoveCount T.tableaux.betaTableau a
            ⟨t.val, by omega⟩ := by
        simpa [u] using hstay
      rw [hstay']
    · right
      dsimp [betaTableauPosition]
      have hmove' : betaRowMoveCount T.tableaux.betaTableau a
          ⟨t.val + 1, by omega⟩ = betaRowMoveCount T.tableaux.betaTableau a
            ⟨t.val, by omega⟩ + 1 := by
        simpa [u] using hmove
      rw [hmove']
      omega
  · have htq : q ≤ t.val := by omega
    let u : Fin (p * J.tupleWidth) :=
      ⟨t.val - q, by
        have htlt := t.isLt
        simp only [finiteFactorStageCount] at htlt
        omega⟩
    by_cases hboundary : t.val = q
    · have hleft : mixedTableauPosition T hp a t.castSucc =
          mixedTableauBoundary T a := by
        rw [mixedTableauPosition_of_le_boundary T hp a t.castSucc (by
          change t.val ≤ q
          omega)]
        have hlast := betaTableauPosition_last T.tableaux.betaTableau a
          (tupleNetworkSource J a) (tupleCoproductTableau_beta_row_bound T a)
        have htlast :
            (⟨t.val, by
              have htlt := t.isLt
              simp only [finiteFactorStageCount] at htlt ⊢
              omega⟩ : Fin (q + 1)) = Fin.last q := by
          apply Fin.ext
          simp [hboundary]
        change betaTableauPosition T.tableaux.betaTableau a (tupleNetworkSource J a)
          (tupleCoproductTableau_beta_row_bound T a)
          ⟨t.val, by
            have htlt := t.isLt
            simp only [finiteFactorStageCount] at htlt ⊢
            omega⟩ = mixedTableauBoundary T a
        rw [htlast]
        apply Fin.ext
        simpa [mixedTableauBoundary] using congrArg Fin.val hlast
      have hright : mixedTableauPosition T hp a t.succ =
          alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a)
            (⟨1, by
              have htlt := t.isLt
              simp only [finiteFactorStageCount] at htlt ⊢
              omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) := by
        have hafter := mixedTableauPosition_of_after_boundary T hp a t.succ (by
          change q < t.val + 1
          omega)
        convert hafter using 1 <;> apply Fin.ext <;> simp [hboundary]
      have hzero : alphaTableauPosition T.tableaux.alphaTableau a
          (mixedTableauBoundary T a) (mixedTableauBoundary_alpha_bound T a) 0 =
          mixedTableauBoundary T a := by
        exact alphaTableauPosition_zero _ _ _ _ hp
      have hstep := alphaTableauPosition_network_step
        T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a) hp
          (⟨0, by
            have htlt := t.isLt
            simp only [finiteFactorStageCount] at htlt ⊢
            omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth))
      unfold NetworkStepAllowed at hstep ⊢
      rw [if_neg (by omega : ¬(0 : ℕ) < 0)] at hstep
      rw [if_neg ht]
      rw [hleft, hright]
      have hzeroVal := congrArg Fin.val hzero
      rw [← hzeroVal]
      simpa [u, hboundary] using hstep
    · have htgt : q < t.val := by omega
      have hleft := mixedTableauPosition_of_after_boundary T hp a t.castSucc (by
        change q < t.val
        omega)
      have hright := mixedTableauPosition_of_after_boundary T hp a t.succ (by
        change q < t.val + 1
        omega)
      let u0 : Fin (finiteFactorStageCount p 0 J.tupleWidth) :=
        ⟨u.val, by
          have hu := u.isLt
          simp only [finiteFactorStageCount] at hu ⊢
          simpa [finiteFactorStageCount] using hu⟩
      have hleft' : mixedTableauPosition T hp a t.castSucc =
          alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a) u0.castSucc := by
        convert hleft using 1 <;> apply Fin.ext <;> simp [u, u0] <;> omega
      have hright' : mixedTableauPosition T hp a t.succ =
          alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a) u0.succ := by
        let sAlpha : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1) :=
          ⟨t.succ.val - q, by
            have htlt := t.isLt
            simp only [finiteFactorStageCount] at htlt ⊢
            omega⟩
        have hright0 : mixedTableauPosition T hp a t.succ =
            alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
              (mixedTableauBoundary_alpha_bound T a) sAlpha := by
          simpa [sAlpha] using hright
        have hsAlpha : sAlpha = u0.succ := by
          apply Fin.ext
          simp [sAlpha, u, u0]
          omega
        rw [hsAlpha] at hright0
        exact hright0
      have hstep := alphaTableauPosition_network_step
        T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a) hp u0
      unfold NetworkStepAllowed at hstep ⊢
      rw [if_neg (by omega : ¬u.val < 0)] at hstep
      rw [if_neg ht]
      rw [hleft', hright']
      simpa [u, u0] using hstep

set_option maxHeartbeats 1000000 in
-- The beta-row collision argument is a finite-cell cardinality proof with dependent row cells.
theorem mixedTableauPosition_beta_strict
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) {a b : Fin r} (hab : a < b)
    (s : Fin (finiteFactorStageCount p q J.tupleWidth + 1))
    (hs : s.val ≤ q) :
    ¬ mixedTableauPosition T hp a s = mixedTableauPosition T hp b s := by
  let TB := T.tableaux.betaTableau
  let sa : Fin (q + 1) := ⟨s.val, by
    have hslt := s.isLt
    simp only [finiteFactorStageCount] at hslt ⊢
    omega⟩
  let N := J.tupleWidth
  have hposA : (mixedTableauPosition T hp a s).val =
      N - (a.rev.val +
        (T.intermediate.betaShape.outer a - betaRowMoveCount TB a sa)) := by
    have h := mixedTableauPosition_of_le_boundary T hp a s hs
    have h' := congrArg Fin.val h
    have hbeta : (mixedTableauPosition T hp a s).val =
        N - (J a.rev - 1) + betaRowMoveCount TB a sa := by
      simpa [betaTableauPosition, N, sa] using h'
    rw [hbeta]
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
  have hposB : (mixedTableauPosition T hp b s).val =
      N - (b.rev.val +
        (T.intermediate.betaShape.outer b - betaRowMoveCount TB b sa)) := by
    have h := mixedTableauPosition_of_le_boundary T hp b s hs
    have h' := congrArg Fin.val h
    have hbeta : (mixedTableauPosition T hp b s).val =
        N - (J b.rev - 1) + betaRowMoveCount TB b sa := by
      simpa [betaTableauPosition, N, sa] using h'
    rw [hbeta]
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
  intro hcoll
  have hcollVal := congrArg Fin.val hcoll
  rw [hposA, hposB] at hcollVal
  have hrev : b.rev.val < a.rev.val := by
    have h := Fin.rev_lt_rev.mpr hab
    exact Fin.mk_lt_mk.mp h
  let xa := T.intermediate.betaShape.outer a - betaRowMoveCount TB a sa
  let xb := T.intermediate.betaShape.outer b - betaRowMoveCount TB b sa
  have hxaN : a.rev.val + xa ≤ N := by
    dsimp [xa, N]
    have houter := T.intermediate.betaShape.outer.rowLength_le_width a
    have hrev' := a.rev.isLt
    have houterEq : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    have hxa_le : T.intermediate.betaShape.outer a -
        betaRowMoveCount TB a sa ≤ T.intermediate.betaShape.outer a := Nat.sub_le _ _
    change a.rev.val + (T.intermediate.betaShape.outer a -
      betaRowMoveCount TB a sa) ≤ N
    rw [houterEq]
    omega
  have hxbN : b.rev.val + xb ≤ N := by
    dsimp [xb, N]
    have houter := T.intermediate.betaShape.outer.rowLength_le_width b
    have hrev' := b.rev.isLt
    have houterEq : T.intermediate.betaShape.outer b =
        J b.rev - (b.rev.val + 1) := rfl
    have hJ := J.value_le_tupleWidth b.rev
    have hpos := J.position_le b.rev
    have hxb_le : T.intermediate.betaShape.outer b -
        betaRowMoveCount TB b sa ≤ T.intermediate.betaShape.outer b := Nat.sub_le _ _
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
    have hadd : T.intermediate.betaShape.inner a + betaRowMoveCount TB a sa ≤
        T.intermediate.betaShape.outer a := by
      calc
        T.intermediate.betaShape.inner a + betaRowMoveCount TB a sa ≤
            T.intermediate.betaShape.inner a +
              (T.intermediate.betaShape.outer a -
                T.intermediate.betaShape.inner a) :=
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
  have hxaoutB : xa < T.intermediate.betaShape.outer b := hxbgt.trans_le hxbout
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
    have hbd' : xb ≤ xa := by simpa [cB, xb] using hbd
    omega
  have hcol := TB.column_weak (x := ⟨(a, cA.val), by
      simpa [FiniteSkewShape.rowCells] using cA.property⟩)
      (y := ⟨(b, cB.val), by
        simpa [FiniteSkewShape.rowCells] using cB.property⟩) rfl hab.le
  have hstage_order : (betaRowStage TB b cB).val ≤
      (betaRowStage TB a cA).val := by
    exact Fin.rev_le_rev.mpr (Fin.mk_le_mk.mpr hcol)
  omega

theorem mixedAlphaBlock_separated
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    {a b : Fin r} (hab : a < b) (i : Fin p) :
    alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
      (mixedTableauBoundary_alpha_bound T a) i (Fin.last J.tupleWidth) <
    alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
      (mixedTableauBoundary_alpha_bound T b) i 0 := by
  let A := T.tableaux.alphaTableau
  have hshape := alphaRowPrefixCount_add_blockCount_le_of_row_lt A hab i
  change alphaRowPrefixCount A a i + alphaRowBlockCount A a i ≤
    alphaRowPrefixCount A b i +
      (T.intermediate.middle a - T.intermediate.middle b) at hshape
  have hboundary :
      (mixedTableauBoundary T a).val +
          (T.intermediate.middle a - T.intermediate.middle b) <
        (mixedTableauBoundary T b).val := by
    rw [mixedTableauBoundary_val, mixedTableauBoundary_val,
      FiniteSkewShape.rowWidth_eq_sub, FiniteSkewShape.rowWidth_eq_sub]
    have hsourceLe : (tupleNetworkSource J a).val ≤
        (tupleNetworkSource J b).val := by
      rw [tupleNetworkSource_val, tupleNetworkSource_val]
      have hrev := Fin.rev_lt_rev.mpr hab
      have hJlt := J.strictMono hrev
      have hJposB := J.position_le b.rev
      omega
    have hsourceDiff :
        (tupleNetworkSource J a).val + (J a.rev - J b.rev) =
          (tupleNetworkSource J b).val := by
      rw [tupleNetworkSource_val, tupleNetworkSource_val]
      let A₀ := J a.rev - 1
      let B₀ := J b.rev - 1
      have hA : A₀ ≤ J.tupleWidth := by
        dsimp [A₀]
        have hposA := J.position_le a.rev
        have hwidthA := J.value_le_tupleWidth a.rev
        omega
      have hBA : B₀ ≤ A₀ := by
        dsimp [A₀, B₀]
        exact Nat.sub_le_sub_right
          (Nat.le_of_lt (J.strictMono (Fin.rev_lt_rev.mpr hab))) 1
      have hsub : A₀ - B₀ = J a.rev - J b.rev := by
        dsimp [A₀, B₀]
        have hposA := J.position_le a.rev
        have hposB := J.position_le b.rev
        have hlt := J.strictMono (Fin.rev_lt_rev.mpr hab)
        omega
      change (J.tupleWidth - A₀) + (J a.rev - J b.rev) =
        J.tupleWidth - B₀
      rw [← hsub]
      exact Nat.sub_add_sub_cancel hA hBA
    have houterGap :
        (J.associatedPart a - J.associatedPart b) < J a.rev - J b.rev := by
      have hgap := containingOuterPartition_diff_add_rev_gap J hab
      have hrev := Fin.rev_lt_rev.mpr hab
      have hrevVal := Fin.mk_lt_mk.mp hrev
      change (J a.rev - (a.rev.val + 1) -
          (J b.rev - (b.rev.val + 1))) < J a.rev - J b.rev
      have hgap' :
          (J a.rev - (a.rev.val + 1) -
            (J b.rev - (b.rev.val + 1))) +
              (a.rev.val - b.rev.val) = J a.rev - J b.rev := by
        simpa [containingOuterPartition] using hgap
      have hrevGap : 1 ≤ a.rev.val - b.rev.val := by omega
      omega
    change (tupleNetworkSource J a).val +
        (J.associatedPart a - T.intermediate.middle a) +
        (T.intermediate.middle a - T.intermediate.middle b) <
      (tupleNetworkSource J b).val +
        (J.associatedPart b - T.intermediate.middle b)
    have hcollapse : J.associatedPart a - T.intermediate.middle a +
        (T.intermediate.middle a - T.intermediate.middle b) =
      J.associatedPart a - T.intermediate.middle b := by
      have hmid := T.intermediate.outer_ge a
      have hanti := T.intermediate.middle.antitone hab.le
      exact Nat.sub_add_sub_cancel hmid hanti
    rw [Nat.add_assoc, hcollapse]
    have hmiddle : T.intermediate.middle b ≤ J.associatedPart b :=
      T.intermediate.outer_ge b
    have houterOrder : J.associatedPart b ≤ J.associatedPart a :=
      J.associatedPart_antitone hab.le
    omega
  rw [alphaRowBlockPosition_last, alphaRowBlockPosition_zero]
  apply Fin.mk_lt_mk.mpr
  unfold alphaRowBlockSource
  change (mixedTableauBoundary T a).val + alphaRowPrefixCount A a i +
      alphaRowBlockCount A a i <
    (mixedTableauBoundary T b).val + alphaRowPrefixCount A b i
  have hle := Nat.add_le_add_left hshape (mixedTableauBoundary T a).val
  omega

theorem mixedTableauPosition_last
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) (a : Fin r) :
    mixedTableauPosition T hp a (Fin.last (finiteFactorStageCount p q J.tupleWidth)) =
      tupleNetworkSink I J hstruct a := by
  let sLast : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1) :=
    Fin.last (finiteFactorStageCount p 0 J.tupleWidth)
  have hafter := mixedTableauPosition_of_after_boundary T hp a
    (Fin.last (finiteFactorStageCount p q J.tupleWidth)) (by
      have hmul : 0 < p * J.tupleWidth := Nat.mul_pos hp hN
      rw [finiteFactorStageCount]
      exact Nat.lt_add_of_pos_right hmul)
  have hidx :
      (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
        have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
        simp only [finiteFactorStageCount] at hlastlt ⊢
        omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) = sLast := by
    apply Fin.ext
    simp only [sLast, Fin.val_last, finiteFactorStageCount, Nat.add_sub_cancel_left,
      Nat.zero_add]
  have hpos :
      alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a)
          (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
            have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
            simp only [finiteFactorStageCount] at hlastlt ⊢
            omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a) sLast := by
    exact congrArg
      (fun k : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1) ↦
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a) k) hidx
  rw [hafter]
  calc
    alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
        (mixedTableauBoundary_alpha_bound T a)
        (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
          have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
          simp only [finiteFactorStageCount] at hlastlt ⊢
          omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
      alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
        (mixedTableauBoundary_alpha_bound T a) sLast := hpos
    _ = ⟨(mixedTableauBoundary T a).val +
        T.intermediate.alphaShape.rowWidth a, by
          exact Nat.lt_succ_of_le (mixedTableauBoundary_alpha_bound T a)⟩ :=
      alphaTableauPosition_sink T.tableaux.alphaTableau a
        (mixedTableauBoundary T a) (mixedTableauBoundary_alpha_bound T a) hp
    _ = tupleNetworkSink I J hstruct a := by
      apply Fin.ext
      change (mixedTableauBoundary T a).val +
          T.intermediate.alphaShape.rowWidth a =
        (tupleNetworkSink I J hstruct a).val
      rw [mixedTableauBoundary_val, FiniteSkewShape.rowWidth_eq_sub,
        FiniteSkewShape.rowWidth_eq_sub]
      change (J.tupleWidth - (J a.rev - 1)) +
          (J.associatedPart a - T.intermediate.middle a) +
          (T.intermediate.middle a - I.associatedPart a) =
        J.tupleWidth - (I a.rev - 1)
      have hinner : I.associatedPart a ≤ T.intermediate.middle a :=
        T.intermediate.inner_le a
      have houter : T.intermediate.middle a ≤ J.associatedPart a :=
        T.intermediate.outer_ge a
      have hcollapse : J.associatedPart a - T.intermediate.middle a +
          (T.intermediate.middle a - I.associatedPart a) =
        J.associatedPart a - I.associatedPart a := by
        exact Nat.sub_add_sub_cancel houter hinner
      rw [Nat.add_assoc, hcollapse]
      have hassoc : J.associatedPart a - I.associatedPart a =
          J a.rev - I a.rev := by
        change J a.rev - (a.rev.val + 1) -
          (I a.rev - (a.rev.val + 1)) = J a.rev - I a.rev
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        have hstruct' := hstruct a.rev
        omega
      rw [hassoc]
      change (J.tupleWidth - (J a.rev - 1)) +
          (J a.rev - I a.rev) = J.tupleWidth - (I a.rev - 1)
      have hJ := J.value_le_tupleWidth a.rev
      have hI := (hstruct a.rev).trans hJ
      have hsub : (J a.rev - 1) - (I a.rev - 1) = J a.rev - I a.rev := by
        have hJpos := J.position_le a.rev
        have hIpos := I.position_le a.rev
        have hstruct' := hstruct a.rev
        omega
      have hJminus : J a.rev - 1 ≤ J.tupleWidth := by omega
      have hImid : I a.rev - 1 ≤ J a.rev - 1 :=
        Nat.sub_le_sub_right (hstruct a.rev) 1
      rw [← hsub]
      exact Nat.sub_add_sub_cancel hJminus hImid

set_option maxHeartbeats 1000000 in
-- The alpha-tail collision argument unfolds one quotient/remainder block at a time.
theorem mixedTableauPosition_alpha_nocollide
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) {a b : Fin r} (hab : a < b)
    (s : Fin (finiteFactorStageCount p q J.tupleWidth + 1))
    (hs : q < s.val) :
    ¬ mixedTableauPosition T hp a s = mixedTableauPosition T hp b s := by
  intro hcoll
  have hN : 0 < J.tupleWidth := by
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  by_cases hinterior : s.val - q < p * J.tupleWidth
  · let u : Fin (p * J.tupleWidth) := ⟨s.val - q, hinterior⟩
    let i : Fin p := alphaStageIndex u
    let k : Fin (J.tupleWidth + 1) :=
      ⟨(s.val - q) % J.tupleWidth, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩
    let sa : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1) := ⟨s.val - q, by
      simp only [finiteFactorStageCount]
      omega⟩
    have hboundA := mixedTableauBoundary_alpha_bound T a
    have hboundB := mixedTableauBoundary_alpha_bound T b
    have hposA := alphaTableauPosition_of_internal
      T.tableaux.alphaTableau a (mixedTableauBoundary T a) hboundA sa hN.ne'
        hinterior
    have hposB := alphaTableauPosition_of_internal
      T.tableaux.alphaTableau b (mixedTableauBoundary T b) hboundB sa hN.ne'
        hinterior
    have hstage : i.val * J.tupleWidth + k.val = sa.val := by
      simpa [i, k, sa, u] using alphaStageIndex_mul_add_mod hN u
    have hstageA :
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            hboundA sa =
          alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            hboundA i k := by
      simpa [i, k, sa, u] using hposA
    have hstageB :
        alphaTableauPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
            hboundB sa =
          alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
            hboundB i k := by
      simpa [i, k, sa, u] using hposB
    have hmixA := mixedTableauPosition_of_after_boundary T hp a s hs
    have hmixB := mixedTableauPosition_of_after_boundary T hp b s hs
    have hmixA' : mixedTableauPosition T hp a s =
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          hboundA sa := by
      simpa [sa] using hmixA
    have hmixB' : mixedTableauPosition T hp b s =
        alphaTableauPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
          hboundB sa := by
      simpa [sa] using hmixB
    have hEqBlock :
        alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            hboundA i k =
          alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
            hboundB i k := by
      calc
        alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
              hboundA i k =
            alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
              hboundA sa := hstageA.symm
        _ = mixedTableauPosition T hp a s := hmixA'.symm
        _ = mixedTableauPosition T hp b s := hcoll
        _ = alphaTableauPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
              hboundB sa := hmixB'
        _ = alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
              hboundB i k := hstageB
    have hsep := mixedAlphaBlock_separated T hab i
    have hleA := alphaBlockPosition_le_endpoint
      (alphaRowBlockSource T.tableaux.alphaTableau a (mixedTableauBoundary T a)
        hboundA i)
      (alphaRowBlockCount T.tableaux.alphaTableau a i)
      (alphaRowBlockSource_add_count_le T.tableaux.alphaTableau a
        (mixedTableauBoundary T a) hboundA i)
      ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
    have hgeB := alphaBlockPosition_ge_source
      (alphaRowBlockSource T.tableaux.alphaTableau b (mixedTableauBoundary T b)
        hboundB i)
      (alphaRowBlockCount T.tableaux.alphaTableau b i)
      (alphaRowBlockSource_add_count_le T.tableaux.alphaTableau b
        (mixedTableauBoundary T b) hboundB i)
      ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
    have hleA' :
        (alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          hboundA i k).val ≤
          (alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            hboundA i (Fin.last J.tupleWidth)).val := by
      rw [alphaRowBlockPosition_last]
      exact hleA
    have hgeB' :
        (alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
          hboundB i 0).val ≤
          (alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
            hboundB i k).val := by
      rw [alphaRowBlockPosition_zero]
      exact hgeB
    have hstrict :
        alphaRowBlockPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            hboundA i k <
          alphaRowBlockPosition T.tableaux.alphaTableau b (mixedTableauBoundary T b)
            hboundB i k := by
      apply Fin.mk_lt_mk.mpr
      exact lt_of_le_of_lt hleA'
        (lt_of_lt_of_le (Fin.mk_lt_mk.mp hsep) hgeB')
    exact (Nat.ne_of_lt (Fin.mk_lt_mk.mp hstrict)) (congrArg Fin.val hEqBlock)
  · have hlast : s = Fin.last (finiteFactorStageCount p q J.tupleWidth) := by
      apply Fin.ext
      have hslt := s.isLt
      simp only [Fin.val_last, finiteFactorStageCount] at hslt ⊢
      omega
    subst s
    have hfinalA := mixedTableauPosition_last T hp hq hN a
    have hfinalB := mixedTableauPosition_last T hp hq hN b
    have hsink : tupleNetworkSink I J hstruct a =
        tupleNetworkSink I J hstruct b := hfinalA.symm.trans (hcoll.trans hfinalB)
    exact (Nat.ne_of_lt (Fin.mk_lt_mk.mp
      (tupleNetworkSink_strictMono I J hstruct hab))) (congrArg Fin.val hsink)

noncomputable def mixedTableauPath
    {p q r : ℕ} (D : FiniteEdreiData p q)
    {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) (a : Fin r) :
    FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
      (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) := by
  let f : Fin (finiteFactorStageCount p q J.tupleWidth + 1) →
      Fin (J.tupleWidth + 1) := mixedTableauPosition T hp a
  have hsource : f 0 = tupleNetworkSource J a := by
    dsimp [f]
    rw [mixedTableauPosition_of_le_boundary T hp a
      (0 : Fin (finiteFactorStageCount p q J.tupleWidth + 1)) (Nat.zero_le _)]
    exact betaTableauPosition_zero _ _ _ _
  have hmul : 0 < p * J.tupleWidth := Nat.mul_pos hp hN
  have hqtotal : q < finiteFactorStageCount p q J.tupleWidth := by
    rw [finiteFactorStageCount]
    exact Nat.lt_add_of_pos_right hmul
  have hlastIndex :
      (⟨finiteFactorStageCount p q J.tupleWidth - q,
        by simp only [finiteFactorStageCount]; omega⟩ :
        Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
        Fin.last (finiteFactorStageCount p 0 J.tupleWidth) := by
    apply Fin.ext
    simp only [Fin.val_last, finiteFactorStageCount, Nat.add_sub_cancel_left, Nat.zero_add]
  have hlast : f (Fin.last (finiteFactorStageCount p q J.tupleWidth)) =
      tupleNetworkSink I J hstruct a := by
    dsimp [f]
    have hafter := mixedTableauPosition_of_after_boundary T hp a
      (Fin.last (finiteFactorStageCount p q J.tupleWidth)) (by
        simpa using hqtotal)
    rw [hafter]
    have halphaIndex :
        (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
          have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
          simp only [finiteFactorStageCount] at hlastlt ⊢
          omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
        Fin.last (finiteFactorStageCount p 0 J.tupleWidth) := by
      apply Fin.ext
      simp only [Fin.val_last, finiteFactorStageCount, Nat.add_sub_cancel_left,
        Nat.zero_add]
    have hpos :
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a)
            (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
              have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
              simp only [finiteFactorStageCount] at hlastlt ⊢
              omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
          alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a)
            (Fin.last (finiteFactorStageCount p 0 J.tupleWidth)) := by
      exact congrArg
        (fun k : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1) ↦
          alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
            (mixedTableauBoundary_alpha_bound T a) k) halphaIndex
    calc
      alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a)
          (⟨(Fin.last (finiteFactorStageCount p q J.tupleWidth)).val - q, by
            have hlastlt := (Fin.last (finiteFactorStageCount p q J.tupleWidth)).isLt
            simp only [finiteFactorStageCount] at hlastlt ⊢
            omega⟩ : Fin (finiteFactorStageCount p 0 J.tupleWidth + 1)) =
        alphaTableauPosition T.tableaux.alphaTableau a (mixedTableauBoundary T a)
          (mixedTableauBoundary_alpha_bound T a)
          (Fin.last (finiteFactorStageCount p 0 J.tupleWidth)) := hpos
      _ = ⟨(mixedTableauBoundary T a).val +
          T.intermediate.alphaShape.rowWidth a, by
            exact Nat.lt_succ_of_le (mixedTableauBoundary_alpha_bound T a)⟩ :=
        alphaTableauPosition_sink T.tableaux.alphaTableau a
          (mixedTableauBoundary T a) (mixedTableauBoundary_alpha_bound T a) hp
      _ = tupleNetworkSink I J hstruct a := by
        apply Fin.ext
        change (mixedTableauBoundary T a).val +
            T.intermediate.alphaShape.rowWidth a =
          (tupleNetworkSink I J hstruct a).val
        rw [mixedTableauBoundary_val, FiniteSkewShape.rowWidth_eq_sub,
          FiniteSkewShape.rowWidth_eq_sub]
        change (J.tupleWidth - (J a.rev - 1)) +
            (J.associatedPart a - T.intermediate.middle a) +
            (T.intermediate.middle a - I.associatedPart a) =
          J.tupleWidth - (I a.rev - 1)
        have hinner : I.associatedPart a ≤ T.intermediate.middle a :=
          T.intermediate.inner_le a
        have houter : T.intermediate.middle a ≤ J.associatedPart a :=
          T.intermediate.outer_ge a
        have hcollapse : J.associatedPart a - T.intermediate.middle a +
            (T.intermediate.middle a - I.associatedPart a) =
          J.associatedPart a - I.associatedPart a := by omega
        rw [Nat.add_assoc, hcollapse]
        have hassoc : J.associatedPart a - I.associatedPart a =
            J a.rev - I a.rev := by
          change J a.rev - (a.rev.val + 1) -
            (I a.rev - (a.rev.val + 1)) = J a.rev - I a.rev
          have hIpos' := I.position_le a.rev
          have hJpos' := J.position_le a.rev
          have hstruct' := hstruct a.rev
          omega
        rw [hassoc]
        change (J.tupleWidth - (J a.rev - 1)) +
            (J a.rev - I a.rev) = J.tupleWidth - (I a.rev - 1)
        have hJ := J.value_le_tupleWidth a.rev
        have hI := (hstruct a.rev).trans hJ
        have hJpos := J.position_le a.rev
        have hIpos := I.position_le a.rev
        have hsub : (J a.rev - 1) - (I a.rev - 1) = J a.rev - I a.rev := by
          omega
        have hJminus : J a.rev - 1 ≤ J.tupleWidth := by omega
        have hImid : I a.rev - 1 ≤ J a.rev - 1 := by
          exact Nat.sub_le_sub_right (hstruct a.rev) 1
        rw [← hsub]
        exact Nat.sub_add_sub_cancel hJminus hImid
  refine { position := f, source_eq := hsource, sink_eq := hlast, valid := ?_ }
  intro t
  change NetworkStepAllowed p q J.tupleWidth t.val
    (mixedTableauPosition T hp a t.castSucc)
    (mixedTableauPosition T hp a t.succ)
  simpa [tupleNetworkBound] using mixedTableauPosition_network_step T hp a t

@[simp] theorem mixedTableauPath_position
    {p q r : ℕ} (D : FiniteEdreiData p q)
    {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) (a : Fin r)
    (s : Fin (finiteFactorStageCount p q (tupleNetworkBound J) + 1)) :
    (mixedTableauPath D T hp hq hN a).position s = mixedTableauPosition T hp a s :=
  rfl

noncomputable def mixedTableauTerm
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) :
    TupleFiniteFactorNetworkTerm D I J hstruct :=
  ⟨Equiv.refl (Fin r), fun a => mixedTableauPath D T hp hq hN a⟩

theorem mixedTableauTerm_good
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) :
    NetworkTermGood (mixedTableauTerm D I J hstruct T hp hq hN) := by
  intro a b hab s hcollision
  have hcollision' :
      mixedTableauPosition T hp a s = mixedTableauPosition T hp b s := by
    simpa only [mixedTableauPath_position] using hcollision
  by_cases hs : s.val ≤ q
  · exact mixedTableauPosition_beta_strict T hp hab s hs hcollision'
  · exact mixedTableauPosition_alpha_nocollide T hp hq hab s (lt_of_not_ge hs) hcollision'

noncomputable def mixedTableauGoodFamily
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) :
    TupleVertexDisjointPathFamily D I J hstruct :=
  ⟨mixedTableauTerm D I J hstruct T hp hq hN,
    mixedTableauTerm_good D I J hstruct T hp hq hN⟩

theorem mixedTableauGoodFamily_intermediate
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) :
    (mixedTableauGoodFamily D I J hstruct T hp hq hN).intermediate = T.intermediate := by
  apply IntermediateRectanglePartition.middle_injective
  apply RectanglePartition.rowLength_injective
  funext a
  apply Fin.ext
  change reflectedWirePart a
      ((mixedTableauPath D T hp hq hN a).position
        (betaBoundaryVertex p q J.tupleWidth)) = T.intermediate.middle a
  rw [mixedTableauPath_position]
  rw [mixedTableauPosition_at_boundary T hp a]
  unfold reflectedWirePart
  rw [mixedTableauBoundary_val, FiniteSkewShape.rowWidth_eq_sub]
  change J.tupleWidth -
      (a.rev.val +
        ((J.tupleWidth - (J a.rev - 1)) +
          (J.associatedPart a - T.intermediate.middle a))) =
    T.intermediate.middle a
  have hJ := J.value_le_tupleWidth a.rev
  have hpos := J.position_le a.rev
  have houter := T.intermediate.outer_ge a
  have hassoc : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
  rw [hassoc]
  have hAssoc : J a.rev - (a.rev.val + 1) =
      (J a.rev - 1) - a.rev.val := by omega
  rw [hAssoc]
  have hA : J a.rev - 1 ≤ J.tupleWidth := by omega
  have hR : a.rev.val ≤ J a.rev - 1 := by omega
  have hM : T.intermediate.middle a ≤ (J a.rev - 1) - a.rev.val := by
    change T.intermediate.middle a ≤ J a.rev - (a.rev.val + 1) at houter
    omega
  omega

theorem betaCellCrossingStage_eq_of_entry_eq
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (xF : (F.intermediate.betaShape).Cell)
    (xG : (G.intermediate.betaShape).Cell)
    (hentry : betaCellEntry F xF = betaCellEntry G xG) :
    betaCellCrossingStage F xF = betaCellCrossingStage G xG := by
  apply Fin.ext
  have hrev := congrArg Fin.rev hentry
  simpa [betaCellEntry] using congrArg Fin.val hrev

theorem alphaCellCrossingStage_eq_of_entry_eq
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (xF : (F.intermediate.alphaShape).Cell)
    (xG : (G.intermediate.alphaShape).Cell)
    (hval : xF.val = xG.val)
    (hentry : alphaCellEntry F xF = alphaCellEntry G xG) :
    alphaCellCrossingStage F xF = alphaCellCrossingStage G xG := by
  have hrev := Fin.rev_injective hentry
  have hquot :
      ((alphaCellCrossingStage F xF).val - q) / J.tupleWidth =
        ((alphaCellCrossingStage G xG).val - q) / J.tupleWidth := by
    simpa [alphaCellEntry] using congrArg Fin.val hrev
  have hdecompF := alphaCellCrossingStage_decomposition F xF
  have hdecompG := alphaCellCrossingStage_decomposition G xG
  have hwire : (alphaCellCrossingWire F xF).val =
      (alphaCellCrossingWire G xG).val := by
    rw [alphaCellCrossingWire_val, alphaCellCrossingWire_val]
    simpa [hval]
  have hdecompF' :
      (alphaCellCrossingStage F xF).val =
        q + (((alphaCellCrossingStage F xF).val - q) / J.tupleWidth) *
            J.tupleWidth + (alphaCellCrossingWire F xF).val := hdecompF
  have hdecompG' :
      (alphaCellCrossingStage G xG).val =
        q + (((alphaCellCrossingStage G xG).val - q) / J.tupleWidth) *
            J.tupleWidth + (alphaCellCrossingWire G xG).val := hdecompG
  rw [← hquot] at hdecompG'
  rw [← hwire] at hdecompG'
  apply Fin.ext
  exact hdecompF'.trans hdecompG'.symm

set_option maxHeartbeats 1000000 in
-- The beta inverse identifies a tableau cell with the unique beta chip crossed by its row.
theorem mixedTableauGoodFamily_betaCellEntry_eq
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) (a : Fin r)
    (c : BetaRowCell T.tableaux.betaTableau a) :
    let F := mixedTableauGoodFamily D I J hstruct T hp hq hN
    let hshape : F.intermediate.betaShape = T.intermediate.betaShape :=
      congrArg (fun U => U.betaShape)
        (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
    let xT : T.intermediate.betaShape.Cell :=
      ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
    let xF : F.intermediate.betaShape.Cell := hshape.symm ▸ xT
    betaCellEntry F xF = T.tableaux.betaTableau.entry xT := by
  let F := mixedTableauGoodFamily D I J hstruct T hp hq hN
  let hshape : F.intermediate.betaShape = T.intermediate.betaShape :=
    congrArg (fun U => U.betaShape)
      (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
  let xT : T.intermediate.betaShape.Cell :=
    ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
  let xF : F.intermediate.betaShape.Cell := hshape.symm ▸ xT
  let ts : Fin (finiteFactorStageCount p q J.tupleWidth) :=
    ⟨(betaRowStage T.tableaux.betaTableau a c).val, by
      have hc := (betaRowStage T.tableaux.betaTableau a c).isLt
      simp only [finiteFactorStageCount]
      omega⟩
  have hval : xF.val = xT.val := by
    simpa [xF] using finiteSkewShape_cell_val_transport hshape.symm xT
  have hrow : xF.val.1 = a := by
    have h := congrArg Prod.fst hval
    simpa [xT] using h
  have hwire : (betaCellCrossingWire F xF).val =
      J.tupleWidth - (a.rev.val + c.val.val + 1) := by
    rw [betaCellCrossingWire_val]
    rw [hval]
  let source : Fin (J.tupleWidth + 1) := tupleNetworkSource J a
  let sink0 : Fin (J.tupleWidth + 1) :=
    ⟨source.val + T.intermediate.betaShape.rowWidth a, by
      have hb := tupleCoproductTableau_beta_row_bound T a
      omega⟩
  have hsum : sink0.val = source.val + T.intermediate.betaShape.rowWidth a := rfl
  let D0 : FiniteEdreiData 0 q :=
    { alpha := fun i => Fin.elim0 i
      beta := D.beta
      gamma := 0
      alpha_pos := fun i => Fin.elim0 i
      beta_pos := D.beta_pos
      gamma_nonneg := by norm_num }
  have hbefore := betaTableauPath_position_before_cell D0 T.tableaux.betaTableau a hsum c
  have hafter := betaTableauPath_position_after_cell D0 T.tableaux.betaTableau a hsum c
  have hbefore' :
      ((F.1.2 a).position ts.castSucc).val =
        (betaCellCrossingWire F xF).val := by
    change ((mixedTableauPath D T hp hq hN a).position ts.castSucc).val = _
    rw [mixedTableauPath_position]
    rw [mixedTableauPosition_of_le_boundary T hp a ts.castSucc (by
      change (betaRowStage T.tableaux.betaTableau a c).val ≤ q
      exact (betaRowStage T.tableaux.betaTableau a c).isLt.le)]
    have hts :
        (⟨ts.castSucc.val, by
          simpa [ts] using Nat.lt_succ_of_lt
            (betaRowStage T.tableaux.betaTableau a c).isLt⟩ : Fin (q + 1)) =
          ⟨(betaRowStage T.tableaux.betaTableau a c).val, by
            simpa using Nat.lt_succ_of_lt
              (betaRowStage T.tableaux.betaTableau a c).isLt⟩ := by
      apply Fin.ext
      rfl
    rw [hts]
    have hbeforePos :
        (betaTableauPosition T.tableaux.betaTableau a (tupleNetworkSource J a)
            (tupleCoproductTableau_beta_row_bound T a)
            ⟨(betaRowStage T.tableaux.betaTableau a c).val, by omega⟩).val =
          (tupleNetworkSource J a).val + T.intermediate.betaShape.outer a -
            (c.val.val + 1) := by
      have h := congrArg Fin.val hbefore
      simpa only [betaTableauPath_position] using h
    have houter : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    rw [houter] at hbeforePos
    rw [hbeforePos]
    rw [hwire]
    change (J.tupleWidth - (J a.rev - 1)) +
        (J a.rev - (a.rev.val + 1)) - (c.val.val + 1) =
      J.tupleWidth - (a.rev.val + c.val.val + 1)
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    have hc := FiniteSkewShape.mem_rowCells.mp c.property
    omega
  have hafter' :
      ((F.1.2 a).position ts.succ).val =
        (betaCellCrossingWire F xF).val + 1 := by
    change ((mixedTableauPath D T hp hq hN a).position ts.succ).val = _
    rw [mixedTableauPath_position]
    rw [mixedTableauPosition_of_le_boundary T hp a ts.succ (by
      change (betaRowStage T.tableaux.betaTableau a c).val + 1 ≤ q
      omega)]
    have hts :
        (⟨ts.succ.val, by
          simpa [ts] using Nat.succ_lt_succ
            (betaRowStage T.tableaux.betaTableau a c).isLt⟩ : Fin (q + 1)) =
          ⟨(betaRowStage T.tableaux.betaTableau a c).val + 1, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hts]
    have hafterPos :
        (betaTableauPosition T.tableaux.betaTableau a (tupleNetworkSource J a)
            (tupleCoproductTableau_beta_row_bound T a)
            ⟨(betaRowStage T.tableaux.betaTableau a c).val + 1, by omega⟩).val =
          (tupleNetworkSource J a).val + T.intermediate.betaShape.outer a -
            c.val.val := by
      have h := congrArg Fin.val hafter
      simpa only [betaTableauPath_position] using h
    have houter : T.intermediate.betaShape.outer a =
        J a.rev - (a.rev.val + 1) := rfl
    rw [houter] at hafterPos
    rw [hafterPos]
    rw [hwire]
    change (J.tupleWidth - (J a.rev - 1)) +
        (J a.rev - (a.rev.val + 1)) - c.val.val =
      J.tupleWidth - (a.rev.val + c.val.val + 1) + 1
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    have hc := FiniteSkewShape.mem_rowCells.mp c.property
    omega
  have hstage : betaCellCrossingStage F xF = ts := by
    rw [← hrow] at hbefore' hafter'
    unfold betaCellCrossingStage
    symm
    apply (F.1.2 xF.val.1).crossingStage_unique
      (betaCellCrossingWire F xF).val
      (betaCell_crossing_bounds F xF).1
      (betaCell_crossing_bounds F xF).2.1
    exact ⟨hbefore', hafter'⟩
  unfold betaCellEntry
  apply Fin.rev_injective
  simp only [Fin.rev_rev]
  apply Fin.ext
  have hstageVal := congrArg Fin.val hstage
  change (betaCellCrossingStage F xF).val =
    (T.tableaux.betaTableau.entry xT).rev.val
  rw [hstageVal]
  rfl

set_option maxHeartbeats 1000000 in
-- The alpha row rank is measured from the mixed beta/alpha boundary.
theorem mixedTableauCell_source_add_tail_eq
    {p q r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (a : Fin r) (c : AlphaRowCell T.tableaux.alphaTableau a) :
    (mixedTableauBoundary T a).val +
        alphaRowPrefixCount T.tableaux.alphaTableau a
          (alphaRowBlock T.tableaux.alphaTableau a c) +
        (Finset.univ.filter fun d : AlphaRowCell T.tableaux.alphaTableau a =>
          c.val.val < d.val.val ∧
            alphaRowBlock T.tableaux.alphaTableau a d =
              alphaRowBlock T.tableaux.alphaTableau a c).card =
      J.tupleWidth - (a.rev.val + c.val.val + 1) := by
  let A := T.tableaux.alphaTableau
  let boundary := mixedTableauBoundary T a
  let hbound := mixedTableauBoundary_alpha_bound T a
  have htail := alphaRowBlockSource_add_tailCount_eq A a boundary hbound c
  have hcell := FiniteSkewShape.mem_rowCells.mp c.property
  have htail' := htail
  change boundary.val + alphaRowPrefixCount A a (alphaRowBlock A a c) +
      (Finset.univ.filter fun d : AlphaRowCell A a =>
        c.val.val < d.val.val ∧ alphaRowBlock A a d = alphaRowBlock A a c).card =
    boundary.val + (T.intermediate.middle a - (c.val.val + 1)) at htail'
  change boundary.val +
      alphaRowPrefixCount A a (alphaRowBlock A a c) +
        (Finset.univ.filter fun d : AlphaRowCell A a =>
          c.val.val < d.val.val ∧ alphaRowBlock A a d = alphaRowBlock A a c).card =
    J.tupleWidth - (a.rev.val + c.val.val + 1)
  rw [htail']
  rw [mixedTableauBoundary_val, FiniteSkewShape.rowWidth_eq_sub]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - T.intermediate.middle a) +
        (T.intermediate.middle a - (c.val.val + 1)) =
    J.tupleWidth - (a.rev.val + c.val.val + 1)
  have hJ := J.value_le_tupleWidth a.rev
  have hpos := J.position_le a.rev
  have hmid := T.intermediate.outer_ge a
  have hcellOuter := hcell.2
  change c.val.val < T.intermediate.middle a at hcellOuter
  change T.intermediate.middle a ≤ J.associatedPart a at hmid
  have hassoc : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
  rw [hassoc] at hmid ⊢
  omega

set_option maxHeartbeats 1000000 in
-- A generic alpha block move lemma isolates the terminal-block arithmetic from the splice.
theorem alphaTableauPosition_move_at_block
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (A : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hN : 0 < N) (i : Fin p) (k : Fin N)
    (hsource : (alphaRowBlockSource A a boundary hbound i).val ≤ k.val)
    (hrank : k.val - (alphaRowBlockSource A a boundary hbound i).val <
      alphaRowBlockCount A a i) :
    (alphaTableauPosition A a boundary hbound
        (alphaBlockStage p 0 N i k).castSucc).val = k.val ∧
      (alphaTableauPosition A a boundary hbound
        (alphaBlockStage p 0 N i k).succ).val = k.val + 1 := by
  have hrowmove := alphaRowBlockPosition_move_of_source_add_rank A a boundary hbound i k
    hsource hrank
  have hstage_cur :
      (alphaBlockStage p 0 N i k).castSucc =
        (⟨i.val * N + k.val, by
          simp only [finiteFactorStageCount]
          have hi := i.isLt
          have hk := k.isLt
          have hstep : i.val * N + k.val < (i.val + 1) * N := by
            calc
              i.val * N + k.val < i.val * N + N := Nat.add_lt_add_left hk _
              _ = (i.val + 1) * N := by simp [Nat.succ_mul]
          have hnext : (i.val + 1) * N ≤ p * N :=
            Nat.mul_le_mul_right N (Nat.succ_le_of_lt hi)
          omega⟩ : Fin (finiteFactorStageCount p 0 N + 1)) := by
    apply Fin.ext
    dsimp [alphaBlockStage]
    omega
  have hpos_cur :
      (alphaTableauPosition A a boundary hbound
        (alphaBlockStage p 0 N i k).castSucc).val = k.val := by
    rw [hstage_cur]
    rw [alphaTableauPosition_at_block_offset A a boundary hbound hN i k]
    exact hrowmove.1
  constructor
  · exact hpos_cur
  · by_cases hsame : k.val + 1 < N
    · let kNext : Fin N := ⟨k.val + 1, hsame⟩
      have hstage_next :
          (alphaBlockStage p 0 N i k).succ =
            (⟨i.val * N + kNext.val, by
              simp only [finiteFactorStageCount]
              have hi := i.isLt
              have hstep : i.val * N + kNext.val < (i.val + 1) * N := by
                calc
                  i.val * N + kNext.val < i.val * N + N := Nat.add_lt_add_left kNext.isLt _
                  _ = (i.val + 1) * N := by simp [Nat.succ_mul]
              have hnext : (i.val + 1) * N ≤ p * N :=
                Nat.mul_le_mul_right N (Nat.succ_le_of_lt hi)
              omega⟩ : Fin (finiteFactorStageCount p 0 N + 1)) := by
        apply Fin.ext
        dsimp [alphaBlockStage, kNext]
        omega
      rw [hstage_next]
      rw [alphaTableauPosition_at_block_offset A a boundary hbound hN i kNext]
      have hkNext :
          (⟨kNext.val, Nat.lt_succ_of_lt kNext.isLt⟩ : Fin (N + 1)) = k.succ := by
        apply Fin.ext
        rfl
      rw [hkNext]
      exact hrowmove.2
    · have hboundary : k.val + 1 = N := by omega
      by_cases hfinal : i.val + 1 = p
      · have hstage_next :
            (alphaBlockStage p 0 N i k).succ =
              Fin.last (finiteFactorStageCount p 0 N) := by
          apply Fin.ext
          simp only [alphaBlockStage, Fin.val_succ, Fin.last, Fin.val_mk,
            finiteFactorStageCount]
          calc
            0 + i.val * N + k.val + 1 = i.val * N + (k.val + 1) := by omega
            _ = i.val * N + N := by rw [hboundary]
            _ = (i.val + 1) * N := by simp [Nat.succ_mul]
            _ = 0 + p * N := by rw [hfinal]; simp
        have hkLast : k.succ = Fin.last N := by
          apply Fin.ext
          exact hboundary
        have hrowEnd :
            (alphaRowBlockPosition A a boundary hbound i (Fin.last N)).val =
              k.val + 1 := by
          rw [← hkLast]
          exact hrowmove.2
        have hprefixlast := alphaRowPrefixCount_add_blockCount_last A a i hfinal
        have hsourceCount :
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i = boundary.val + S.rowWidth a := by
          unfold alphaRowBlockSource
          change boundary.val + alphaRowPrefixCount A a i +
              alphaRowBlockCount A a i = boundary.val + S.rowWidth a
          calc
            boundary.val + alphaRowPrefixCount A a i + alphaRowBlockCount A a i =
                boundary.val + (alphaRowPrefixCount A a i + alphaRowBlockCount A a i) := by omega
            _ = boundary.val + S.rowWidth a := by rw [hprefixlast]
        rw [hstage_next]
        rw [alphaTableauPosition_last A a boundary hbound (by exact Nat.ne_of_gt hN)]
        rw [alphaRowBoundaryPosition_last]
        have hwidth : boundary.val + S.rowWidth a = k.val + 1 := by
          calc
            boundary.val + S.rowWidth a =
                (alphaRowBlockSource A a boundary hbound i).val +
                  alphaRowBlockCount A a i := hsourceCount.symm
            _ = (alphaRowBlockPosition A a boundary hbound i (Fin.last N)).val := by
              symm
              exact congrArg Fin.val (alphaRowBlockPosition_last A a boundary hbound i)
            _ = k.val + 1 := hrowEnd
        exact hwidth
      · have hiNext : i.val + 1 < p := by omega
        let iNext : Fin p := ⟨i.val + 1, hiNext⟩
        have hstage_next :
            (alphaBlockStage p 0 N i k).succ =
              (⟨iNext.val * N, by
                simp only [finiteFactorStageCount]
                have hi := iNext.isLt
                have hmul := Nat.mul_lt_mul_of_pos_right iNext.isLt hN
                omega⟩ : Fin (finiteFactorStageCount p 0 N + 1)) := by
          apply Fin.ext
          dsimp [alphaBlockStage, iNext]
          calc
            0 + i.val * N + k.val + 1 = i.val * N + (k.val + 1) := by omega
            _ = i.val * N + N := by rw [hboundary]
            _ = (i.val + 1) * N := by simp [Nat.succ_mul]
        have hkLast : k.succ = Fin.last N := by
          apply Fin.ext
          exact hboundary
        have hrowEnd :
            (alphaRowBlockPosition A a boundary hbound i (Fin.last N)).val =
              k.val + 1 := by
          rw [← hkLast]
          exact hrowmove.2
        have hsourceCount :
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i = k.val + 1 := by
          calc
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i =
              (alphaRowBlockPosition A a boundary hbound i (Fin.last N)).val := by
                symm
                exact congrArg Fin.val
                  (alphaRowBlockPosition_last A a boundary hbound i)
            _ = k.val + 1 := hrowEnd
        rw [hstage_next]
        rw [alphaTableauPosition_at_block_boundary A a boundary hbound hN iNext]
        rw [alphaRowBlockSource_succ A a boundary hbound i hiNext]
        exact hsourceCount

set_option maxHeartbeats 1000000 in
-- The alpha inverse identifies a tableau cell with its reflected alpha block and wire.
theorem mixedTableauGoodFamily_alphaCellEntry_eq
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) (a : Fin r)
    (c : AlphaRowCell T.tableaux.alphaTableau a) :
    let F := mixedTableauGoodFamily D I J hstruct T hp hq hN
    let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
      congrArg (fun U => U.alphaShape)
        (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
    let xT : T.intermediate.alphaShape.Cell :=
      ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
    let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
    alphaCellEntry F xF = T.tableaux.alphaTableau.entry xT := by
  let F := mixedTableauGoodFamily D I J hstruct T hp hq hN
  let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
    congrArg (fun U => U.alphaShape)
      (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
  let xT : T.intermediate.alphaShape.Cell :=
    ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
  let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
  let A := T.tableaux.alphaTableau
  let boundary := mixedTableauBoundary T a
  let hbound := mixedTableauBoundary_alpha_bound T a
  let i : Fin p := alphaRowBlock A a c
  let k : Fin (tupleNetworkBound J) :=
    ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
      have hc := FiniteSkewShape.mem_rowCells.mp c.property
      have hcOuter := hc.2
      change c.val.val < T.intermediate.middle a at hcOuter
      have hmid := T.intermediate.outer_ge a
      have hJ := J.value_le_tupleWidth a.rev
      have hpos := J.position_le a.rev
      change T.intermediate.middle a ≤ J.associatedPart a at hmid
      have hassoc : J.associatedPart a = J a.rev - (a.rev.val + 1) := rfl
      rw [hassoc] at hmid
      exact Nat.sub_lt (by omega) (by omega)⟩
  have hval : xF.val = xT.val := by
    simpa [xF] using finiteSkewShape_cell_val_transport hshape.symm xT
  have hrow : xF.val.1 = a := by
    have h := congrArg Prod.fst hval
    simpa [xT] using h
  have hcol : xF.val.2.val = c.val.val := by
    have h := congrArg (fun z : Fin r × Fin (tupleNetworkBound J) => z.2.val) hval
    simpa [xT] using h
  have hwire : (alphaCellCrossingWire F xF).val = k.val := by
    rw [alphaCellCrossingWire_val]
    rw [hrow, hcol]
  have htail := mixedTableauCell_source_add_tail_eq T a c
  have htail' :
      (alphaRowBlockSource A a boundary hbound i).val +
          (Finset.univ.filter fun d : AlphaRowCell A a =>
            c.val.val < d.val.val ∧ alphaRowBlock A a d = i).card = k.val := by
    unfold alphaRowBlockSource
    simpa [A, boundary, hbound, i, k] using htail
  have htail_lt :
      (Finset.univ.filter fun d : AlphaRowCell A a =>
        c.val.val < d.val.val ∧ alphaRowBlock A a d = i).card <
          alphaRowBlockCount A a i := by
    simpa [i] using alphaRowBlockTailCount_lt_blockCount A a c
  have hsource : (alphaRowBlockSource A a boundary hbound i).val ≤ k.val := by
    omega
  have hrank : k.val - (alphaRowBlockSource A a boundary hbound i).val <
      alphaRowBlockCount A a i := by
    omega
  have hmove := alphaTableauPosition_move_at_block A a boundary hbound hN i k
    hsource hrank
  have hbefore' :
      ((F.1.2 a).position
        (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc).val = k.val := by
    change ((mixedTableauPath D T hp hq hN a).position
      (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc).val = k.val
    rw [mixedTableauPath_position]
    by_cases hs : q < (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc.val
    · rw [mixedTableauPosition_of_after_boundary T hp a _ hs]
      have hidx :
          (⟨(alphaBlockStage p q (tupleNetworkBound J) i k).castSucc.val - q, by
            have hslt := (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc.isLt
            simp only [finiteFactorStageCount] at hslt ⊢
            omega⟩ : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) =
            (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc := by
        apply Fin.ext
        dsimp [alphaBlockStage]
        omega
      rw [hidx]
      exact hmove.1
    · have hs' :
          (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc.val = q := by
        have hle :
            (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc.val ≤ q :=
          Nat.le_of_not_gt hs
        dsimp [alphaBlockStage]
        dsimp [alphaBlockStage] at hle
        omega
      have hNpos : 0 < tupleNetworkBound J := hN
      have hsum : i.val * tupleNetworkBound J + k.val = 0 := by
        dsimp [alphaBlockStage] at hs'
        omega
      have hprod : i.val * tupleNetworkBound J = 0 := by omega
      have hi0 : i.val = 0 := by
        rcases Nat.mul_eq_zero.mp hprod with hi0 | hN0
        · exact hi0
        · exact False.elim (Nat.ne_of_gt hNpos hN0)
      have hk0 : k.val = 0 := by omega
      dsimp [alphaBlockStage] at hs'
      have hidx0 :
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc =
            (0 : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) := by
        apply Fin.ext
        dsimp [alphaBlockStage]
        omega
      have hboundary :
          (alphaBlockStage p q (tupleNetworkBound J) i k).castSucc =
            betaBoundaryVertex p q (tupleNetworkBound J) := by
        apply Fin.ext
        simp [alphaBlockStage, betaBoundaryVertex, hs']
      rw [hboundary, mixedTableauPosition_at_boundary]
      have hmove0 := hmove.1
      rw [hidx0, alphaTableauPosition_zero A a boundary hbound hp] at hmove0
      exact hmove0
  have hafter' :
      ((F.1.2 a).position
        (alphaBlockStage p q (tupleNetworkBound J) i k).succ).val = k.val + 1 := by
    change ((mixedTableauPath D T hp hq hN a).position
      (alphaBlockStage p q (tupleNetworkBound J) i k).succ).val = k.val + 1
    rw [mixedTableauPath_position]
    have hs : q < (alphaBlockStage p q (tupleNetworkBound J) i k).succ.val := by
      dsimp [alphaBlockStage]
      omega
    rw [mixedTableauPosition_of_after_boundary T hp a _ hs]
    have hidx :
        (⟨(alphaBlockStage p q (tupleNetworkBound J) i k).succ.val - q, by
          have hslt := (alphaBlockStage p q (tupleNetworkBound J) i k).succ.isLt
          simp only [finiteFactorStageCount] at hslt ⊢
          omega⟩ : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) =
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ := by
      apply Fin.ext
      dsimp [alphaBlockStage]
      omega
    rw [hidx]
    exact hmove.2
  have hstage : alphaCellCrossingStage F xF =
      alphaBlockStage p q (tupleNetworkBound J) i k := by
    rw [← hrow] at hbefore' hafter'
    rw [← hwire] at hbefore' hafter'
    unfold alphaCellCrossingStage
    symm
    apply (F.1.2 xF.val.1).crossingStage_unique
      (alphaCellCrossingWire F xF).val
      (alphaCell_crossing_bounds F xF).1
      (alphaCell_crossing_bounds F xF).2.1
    exact ⟨hbefore', hafter'⟩
  change alphaCellEntry F xF = T.tableaux.alphaTableau.entry xT
  let eF : Fin p :=
    ⟨((alphaCellCrossingStage F xF).val - q) /
        J.tupleWidth, alphaCellCrossingStage_alpha_index_bound F xF⟩
  have hstageVal := congrArg Fin.val hstage
  have hdiv : eF.val = i.val := by
    dsimp [eF]
    rw [hstageVal]
    simp only [alphaBlockStage, tupleNetworkBound]
    have hsub : q + i.val * J.tupleWidth + k.val - q =
        i.val * J.tupleWidth + k.val := by omega
    rw [hsub]
    change (i.val * J.tupleWidth + k.val) / J.tupleWidth = i.val
    rw [Nat.mul_comm i.val J.tupleWidth, Nat.mul_add_div hN,
      Nat.div_eq_of_lt k.isLt]
    simp
  have hfin : eF = i := by
    apply Fin.ext
    exact hdiv
  change eF.rev = T.tableaux.alphaTableau.entry xT
  rw [hfin]
  simpa [A, i, alphaRowBlock, xT]

set_option maxHeartbeats 1000000 in
-- Equal mixed canonical tableaux determine each path by its beta or alpha wire crossings.
theorem canonicalGoodTableauMap_injective_mixed_positiveWidth
    {p q r : ℕ} (D : FiniteEdreiData p q) (hp : 0 < p) (hq : 0 < q)
    (I J : IncreasingIndexTuple r) (hN : 0 < J.tupleWidth)
    (hstruct : StructurallyAdmissible I J) :
    Function.Injective (@canonicalGoodTableauMap p q r D I J hstruct) := by
  intro F G hT
  have hpermF := tupleNetwork_good_perm_eq_refl F.1 F.2
  have hpermG := tupleNetwork_good_perm_eq_refl G.1 G.2
  apply Subtype.ext
  apply networkTerm_ext
  · rw [hpermF, hpermG]
  · intro a s
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
    have hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
    have hcross : ∀ (k : ℕ)
        (hsource : (tupleNetworkSource J a).val ≤ k)
        (hsink : k < (tupleNetworkSink I J hstruct a).val),
        PF.crossingStage k hsource hsink = PG.crossingStage k hsource hsink := by
      intro k hsource hsink
      let cval := J.tupleWidth - (a.rev.val + k + 1)
      have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIpos := I.position_le a.rev
        have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        omega
      have hcN : cval < J.tupleWidth := by
        dsimp [cval]
        omega
      let c : Fin J.tupleWidth := ⟨cval, hcN⟩
      have houter : cval < J.associatedPart a := by
        change cval < J a.rev - (a.rev.val + 1)
        change J.tupleWidth - (a.rev.val + k + 1) <
          J a.rev - (a.rev.val + 1)
        change J.tupleWidth - (J a.rev - 1) ≤ k at hsource
        omega
      have hinner : I.associatedPart a ≤ cval := by
        change I a.rev - (a.rev.val + 1) ≤ cval
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        omega
      have hmiddleEq :
          (TupleVertexDisjointPathFamily.intermediate F).middle a =
            (TupleVertexDisjointPathFamily.intermediate G).middle a := by
        exact congrArg (fun M ↦ M.middle a) hI
      by_cases hbeta : (TupleVertexDisjointPathFamily.intermediate F).middle a ≤ cval
      · have hcellF :
            (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate F).betaShape.cells := by
          apply FiniteSkewShape.mem_cells.mpr
          change (TupleVertexDisjointPathFamily.intermediate F).middle a ≤ cval ∧
            cval < J.associatedPart a
          exact ⟨hbeta, houter⟩
        have hcellG :
            (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate G).betaShape.cells := by
          apply FiniteSkewShape.mem_cells.mpr
          change (TupleVertexDisjointPathFamily.intermediate G).middle a ≤ cval ∧
            cval < J.associatedPart a
          exact ⟨by simpa [hmiddleEq] using hbeta, houter⟩
        let xF : (TupleVertexDisjointPathFamily.intermediate F).betaShape.Cell :=
          ⟨(a, c), hcellF⟩
        let xG : (TupleVertexDisjointPathFamily.intermediate G).betaShape.Cell :=
          ⟨(a, c), hcellG⟩
        have hwireF : (betaCellCrossingWire F xF).val = k := by
          rw [betaCellCrossingWire_val]
          change J.tupleWidth -
            (a.rev.val + (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
          have hsub := Nat.sub_add_cancel hsum
          omega
        have hwireG : (betaCellCrossingWire G xG).val = k := by
          rw [betaCellCrossingWire_val]
          change J.tupleWidth -
            (a.rev.val + (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
          have hsub := Nat.sub_add_cancel hsum
          omega
        have hentry := tupleCoproductTableauOfPathFamily_beta_entry_injective F G hT xF
        have hstage : betaCellCrossingStage F xF = betaCellCrossingStage G xG := by
          apply betaCellCrossingStage_eq_of_entry_eq F G xF xG hentry
        have hPFstage : betaCellCrossingStage F xF = PF.crossingStage k hsource hsink := by
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
        have hPGstage : betaCellCrossingStage G xG = PG.crossingStage k hsource hsink := by
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
        exact hPFstage.symm.trans (hstage.trans hPGstage)
      · have halpha : cval < (TupleVertexDisjointPathFamily.intermediate F).middle a :=
          Nat.lt_of_not_ge hbeta
        have hcellF :
            (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate F).alphaShape.cells := by
          apply FiniteSkewShape.mem_cells.mpr
          change I.associatedPart a ≤ cval ∧
            cval < (TupleVertexDisjointPathFamily.intermediate F).middle a
          exact ⟨hinner, halpha⟩
        have hcellG :
            (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate G).alphaShape.cells := by
          apply FiniteSkewShape.mem_cells.mpr
          change I.associatedPart a ≤ cval ∧
            cval < (TupleVertexDisjointPathFamily.intermediate G).middle a
          exact ⟨hinner, by simpa [hmiddleEq] using halpha⟩
        let xF : (TupleVertexDisjointPathFamily.intermediate F).alphaShape.Cell :=
          ⟨(a, c), hcellF⟩
        let xG : (TupleVertexDisjointPathFamily.intermediate G).alphaShape.Cell :=
          ⟨(a, c), hcellG⟩
        have hwireF : (alphaCellCrossingWire F xF).val = k := by
          rw [alphaCellCrossingWire_val]
          change J.tupleWidth -
            (a.rev.val + (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
          have hsub := Nat.sub_add_cancel hsum
          omega
        have hwireG : (alphaCellCrossingWire G xG).val = k := by
          rw [alphaCellCrossingWire_val]
          change J.tupleWidth -
            (a.rev.val + (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
          have hsub := Nat.sub_add_cancel hsum
          omega
        have hentry := tupleCoproductTableauOfPathFamily_alpha_entry_injective F G hT xF
        have hstage : alphaCellCrossingStage F xF = alphaCellCrossingStage G xG := by
          apply alphaCellCrossingStage_eq_of_entry_eq F G xF xG
          · rfl
          · exact hentry
        have hPFstage : alphaCellCrossingStage F xF = PF.crossingStage k hsource hsink := by
          apply PF.crossingStage_unique
          have hspec := alphaCellCrossingStage_spec F xF
          constructor
          · change ((F.1.2 a).position (alphaCellCrossingStage F xF).castSucc).val = k
            calc
              _ = (alphaCellCrossingWire F xF).val := by simpa [xF] using hspec.1
              _ = k := hwireF
          · change ((F.1.2 a).position (alphaCellCrossingStage F xF).succ).val = k + 1
            calc
              _ = (alphaCellCrossingWire F xF).val + 1 := by simpa [xF] using hspec.2
              _ = k + 1 := by rw [hwireF]
        have hPGstage : alphaCellCrossingStage G xG = PG.crossingStage k hsource hsink := by
          apply PG.crossingStage_unique
          have hspec := alphaCellCrossingStage_spec G xG
          constructor
          · change ((G.1.2 a).position (alphaCellCrossingStage G xG).castSucc).val = k
            calc
              _ = (alphaCellCrossingWire G xG).val := by simpa [xG] using hspec.1
              _ = k := hwireG
          · change ((G.1.2 a).position (alphaCellCrossingStage G xG).succ).val = k + 1
            calc
              _ = (alphaCellCrossingWire G xG).val + 1 := by simpa [xG] using hspec.2
              _ = k + 1 := by rw [hwireG]
        exact hPFstage.symm.trans (hstage.trans hPGstage)
    have hpath := FiniteFactorPath.ext_of_crossingStage_eq PF PG hcross
    have hpos := congrArg (fun P => P.position s) hpath
    simpa [PF, PG] using hpos

set_option maxHeartbeats 1000000 in
-- The explicit mixed splice reconstructs every alpha and beta entry of the source tableau.
theorem canonicalGoodTableauMap_mixed_positiveWidth
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := q) I J hstruct)
    (hp : 0 < p) (hq : 0 < q) (hN : 0 < J.tupleWidth) :
    canonicalGoodTableauMap (mixedTableauGoodFamily D I J hstruct T hp hq hN) = T := by
  let F := mixedTableauGoodFamily D I J hstruct T hp hq hN
  let U := canonicalGoodTableauMap F
  have hmid : U.intermediate = T.intermediate := by
    change (tupleCoproductTableauOfPathFamily F).intermediate = T.intermediate
    simpa [F, U] using mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN
  apply tupleCoproductTableau_eq_of_intermediate_eq_of_entries_eq U T hmid
  · funext a c
    by_cases hU : (a, c) ∈ U.intermediate.alphaShape.cells
    · have hT : (a, c) ∈ T.intermediate.alphaShape.cells := by
        rw [← hmid]
        exact hU
      let xU : U.intermediate.alphaShape.Cell := ⟨(a, c), hU⟩
      let cRow : AlphaRowCell T.tableaux.alphaTableau a :=
        ⟨c, by simpa [FiniteSkewShape.rowCells] using hT⟩
      let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
        congrArg (fun V => V.alphaShape)
          (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
      let xT : T.intermediate.alphaShape.Cell := ⟨(a, c), hT⟩
      let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
      have hentry0 := mixedTableauGoodFamily_alphaCellEntry_eq
        D I J hstruct T hp hq hN a cRow
      have hentry : alphaCellEntry F xF = T.tableaux.alphaTableau.entry xT := by
        simpa [F, hshape, xT, xF, cRow] using hentry0
      have hval : xF.val = xU.val := by
        calc
          xF.val = xT.val := finiteSkewShape_cell_val_transport hshape.symm xT
          _ = xU.val := by rfl
      have hcell : xF = xU := by
        apply Subtype.ext
        exact hval
      have hcanon : U.tableaux.alphaTableau.entry xU = alphaCellEntry F xU := by
        change (tupleCoproductTableauOfPathFamily F).tableaux.alphaTableau.entry xU = _
        exact tupleCoproductTableauOfPathFamily_alpha_entry F xU
      unfold tupleCoproductAlphaEntryAt
      rw [dif_pos hU, dif_pos hT]
      congr 1
      change U.tableaux.alphaTableau.entry xU =
        T.tableaux.alphaTableau.entry xT
      calc
        U.tableaux.alphaTableau.entry xU = alphaCellEntry F xU := hcanon
        _ = alphaCellEntry F xF := by rw [hcell]
        _ = T.tableaux.alphaTableau.entry xT := hentry
    · have hT : ¬(a, c) ∈ T.intermediate.alphaShape.cells := by
        intro h
        apply hU
        rw [hmid]
        exact h
      simp [tupleCoproductAlphaEntryAt, hU, hT]
  · funext a c
    by_cases hU : (a, c) ∈ U.intermediate.betaShape.cells
    · have hT : (a, c) ∈ T.intermediate.betaShape.cells := by
        rw [← hmid]
        exact hU
      let xU : U.intermediate.betaShape.Cell := ⟨(a, c), hU⟩
      let cRow : BetaRowCell T.tableaux.betaTableau a :=
        ⟨c, by simpa [FiniteSkewShape.rowCells] using hT⟩
      let hshape : F.intermediate.betaShape = T.intermediate.betaShape :=
        congrArg (fun V => V.betaShape)
          (mixedTableauGoodFamily_intermediate D I J hstruct T hp hq hN)
      let xT : T.intermediate.betaShape.Cell := ⟨(a, c), hT⟩
      let xF : F.intermediate.betaShape.Cell := hshape.symm ▸ xT
      have hentry0 := mixedTableauGoodFamily_betaCellEntry_eq
        D I J hstruct T hp hq hN a cRow
      have hentry : betaCellEntry F xF = T.tableaux.betaTableau.entry xT := by
        simpa [F, hshape, xT, xF, cRow] using hentry0
      have hval : xF.val = xU.val := by
        calc
          xF.val = xT.val := finiteSkewShape_cell_val_transport hshape.symm xT
          _ = xU.val := by rfl
      have hcell : xF = xU := by
        apply Subtype.ext
        exact hval
      have hcanon : U.tableaux.betaTableau.entry xU = betaCellEntry F xU := by
        change (tupleCoproductTableauOfPathFamily F).tableaux.betaTableau.entry xU = _
        exact tupleCoproductTableauOfPathFamily_beta_entry F xU
      unfold tupleCoproductBetaEntryAt
      rw [dif_pos hU, dif_pos hT]
      congr 1
      change U.tableaux.betaTableau.entry xU =
        T.tableaux.betaTableau.entry xT
      calc
        U.tableaux.betaTableau.entry xU = betaCellEntry F xU := hcanon
        _ = betaCellEntry F xF := by rw [hcell]
        _ = T.tableaux.betaTableau.entry xT := hentry
    · have hT : ¬(a, c) ∈ T.intermediate.betaShape.cells := by
        intro h
        apply hU
        rw [hmid]
        exact h
      simp [tupleCoproductBetaEntryAt, hU, hT]

theorem canonicalGoodTableauMap_bijective_mixed_positiveWidth
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (hp : 0 < p) (hq : 0 < q)
    (I J : IncreasingIndexTuple r) (hN : 0 < J.tupleWidth)
    (hstruct : StructurallyAdmissible I J) :
    Function.Bijective (@canonicalGoodTableauMap p q r D I J hstruct) :=
  ⟨canonicalGoodTableauMap_injective_mixed_positiveWidth D hp hq I J hN hstruct,
    fun T => ⟨mixedTableauGoodFamily D I J hstruct T hp hq hN,
      canonicalGoodTableauMap_mixed_positiveWidth D I J hstruct T hp hq hN⟩⟩

set_option maxHeartbeats 1000000 in
-- If the reflected width is zero, the index tuple has no rows and both sides are singleton.
theorem canonicalGoodTableauMap_bijective_mixed_zeroWidth
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (hp : 0 < p) (hq : 0 < q)
    (I J : IncreasingIndexTuple r) (hN : J.tupleWidth = 0)
    (hstruct : StructurallyAdmissible I J) :
    Function.Bijective (@canonicalGoodTableauMap p q r D I J hstruct) := by
  cases r with
  | zero =>
      let term : TupleFiniteFactorNetworkTerm D I J hstruct :=
        ⟨Equiv.refl (Fin 0), fun a => Fin.elim0 a⟩
      let good : NetworkTermGood term := by
        intro a
        exact Fin.elim0 a
      let x : {y : TupleFiniteFactorNetworkTerm D I J hstruct // NetworkTermGood y} :=
        ⟨term, good⟩
      constructor
      · intro y z hmap
        apply Subtype.ext
        apply networkTerm_ext
        · exact Subsingleton.elim _ _
        · intro a
          exact Fin.elim0 a
      · intro T
        refine ⟨x, ?_⟩
        let U := canonicalGoodTableauMap x
        have hmid : U.intermediate = T.intermediate := by
          apply IntermediateRectanglePartition.middle_injective
          apply RectanglePartition.rowLength_injective
          funext a
          exact Fin.elim0 a
        apply tupleCoproductTableau_eq_of_intermediate_eq_of_entries_eq U T hmid
        · funext a
          exact Fin.elim0 a
        · funext a
          exact Fin.elim0 a
  | succ r =>
      have hpos := J.position_le (0 : Fin (Nat.succ r))
      have hval := J.value_le_tupleWidth (0 : Fin (Nat.succ r))
      exfalso
      omega

noncomputable def canonicalGoodBijectionBridge_mixed
    {p q : ℕ} (D : FiniteEdreiData p q)
    (hp : 0 < p) (hq : 0 < q) (hgamma : D.gamma = 0) :
    CanonicalGoodBijectionBridge D where
  gamma_eq_zero := hgamma
  bijective r I J hstruct := by
    by_cases hN : 0 < J.tupleWidth
    · exact canonicalGoodTableauMap_bijective_mixed_positiveWidth D hp hq I J hN hstruct
    · exact canonicalGoodTableauMap_bijective_mixed_zeroWidth D hp hq I J
        (Nat.eq_zero_of_not_pos hN) hstruct

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_mixed
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (hp : 0 < p) (hq : 0 < q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
        tupleCoproductWeight D I J hstruct T :=
  finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection hgamma
    ((canonicalGoodBijectionBridge_mixed D hp hq hgamma).bijective r I J hstruct)

theorem finiteFactorMinor_pos_iff_indexHook_mixed
    {p q r : ℕ} (D : FiniteEdreiData p q)
    (hp : 0 < p) (hq : 0 < q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q :=
  (canonicalGoodBijectionBridge_mixed D hp hq hgamma).finiteFactorMinor_pos_iff_indexHook I J

noncomputable def canonicalGoodBijectionBridge_gamma_zero
    {p q : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0) :
    CanonicalGoodBijectionBridge D := by
  cases p with
  | zero => exact canonicalGoodBijectionBridge_p_zero D hgamma
  | succ p =>
      cases q with
      | zero => exact canonicalGoodBijectionBridge_p_pos_q_zero D (Nat.succ_pos p) hgamma
      | succ q =>
          exact canonicalGoodBijectionBridge_mixed D (Nat.succ_pos p) (Nat.succ_pos q) hgamma

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_gamma_zero
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := q) I J hstruct,
        tupleCoproductWeight D I J hstruct T :=
  finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection hgamma
    ((canonicalGoodBijectionBridge_gamma_zero D hgamma).bijective r I J hstruct)

theorem finiteFactorMinor_pos_iff_indexHook_gamma_zero
    {p q r : ℕ} (D : FiniteEdreiData p q) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p q :=
  (canonicalGoodBijectionBridge_gamma_zero D hgamma).finiteFactorMinor_pos_iff_indexHook I J

end

end ToeplitzPositroids.Edrei
