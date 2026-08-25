import ToeplitzPositroids.Edrei.TableauAlphaBijection

/-!
# Arithmetic for splicing several alpha blocks

The alpha part of the finite network is a concatenation of `p` blocks, each with `N` elementary
chips.  This file makes the quotient/remainder decomposition of an alpha stage explicit, defines
the rowwise vertex position read from an alpha tableau, and completes the converse construction in
the `q = 0` slice.  The mixed beta/alpha splice and its converse are completed in
`TableauMixedSplice`.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

theorem alphaStageIndex_mul_add_mod
    {p N : ℕ} (hN : 0 < N) (u : Fin (p * N)) :
    (alphaStageIndex u).val * N + u.val % N = u.val := by
  simpa [alphaStageIndex, Nat.mul_comm] using Nat.div_add_mod u.val N

theorem alphaStageIndex_remainder_lt
    {p N : ℕ} (hN : 0 < N) (u : Fin (p * N)) :
    u.val % N < N :=
  Nat.mod_lt _ hN

theorem alphaStageIndex_zero
    {p N : ℕ} (hN : 0 < N) (hp : 0 < p) :
    alphaStageIndex (⟨0, Nat.mul_pos hp hN⟩ : Fin (p * N)) =
      (⟨0, hp⟩ : Fin p) := by
  apply Fin.ext
  simp [alphaStageIndex, hN]

theorem alphaStageIndex_succ_same_block
    {p N : ℕ} (hN : 0 < N) {u : Fin (p * N)}
    (hrem : u.val % N + 1 < N) :
    alphaStageIndex (⟨u.val + 1, by
      have hdecomp : u.val / N * N + u.val % N = u.val := by
        simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
      have hqbound : u.val / N < p := (alphaStageIndex u).isLt
      calc
        u.val + 1 = u.val / N * N + (u.val % N + 1) := by omega
        _ < u.val / N * N + N := Nat.add_lt_add_left hrem _
        _ = (u.val / N + 1) * N := by simp [Nat.succ_mul]
        _ ≤ p * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hqbound)⟩ : Fin (p * N)) =
      alphaStageIndex u := by
  apply Fin.ext
  change (u.val + 1) / N = u.val / N
  have hdecomp : u.val / N * N + u.val % N = u.val := by
    simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
  exact Nat.div_eq_of_lt_le
    ((Nat.div_mul_le_self u.val N).trans (Nat.le_succ _))
    (by
      calc
        u.val + 1 = u.val / N * N + (u.val % N + 1) := by omega
        _ < u.val / N * N + N := Nat.add_lt_add_left hrem _
        _ = (u.val / N + 1) * N := by simp [Nat.succ_mul])

theorem alphaStageIndex_succ_next_block
    {p N : ℕ} (hN : 0 < N) {u : Fin (p * N)}
    (hrem : u.val % N + 1 = N) (hp : (alphaStageIndex u).val + 1 < p) :
    alphaStageIndex (⟨u.val + 1, by
      have hdecomp : u.val / N * N + u.val % N = u.val := by
        simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
      have hqbound : u.val / N < p := (alphaStageIndex u).isLt
      calc
        u.val + 1 = u.val / N * N + (u.val % N + 1) := by omega
        _ = (u.val / N + 1) * N := by simpa [hrem, Nat.succ_mul] using hdecomp
        _ < p * N := (Nat.mul_lt_mul_right hN).2 hp⟩ : Fin (p * N)) =
      ⟨(alphaStageIndex u).val + 1, hp⟩ := by
  apply Fin.ext
  change (u.val + 1) / N = (alphaStageIndex u).val + 1
  have hdecomp : u.val / N * N + u.val % N = u.val := by
    simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
  have hindex : (alphaStageIndex u).val = u.val / N := rfl
  rw [hindex]
  exact Nat.div_eq_of_lt_le
    (by
      calc
        (u.val / N + 1) * N = u.val / N * N + N := by simp [Nat.succ_mul]
        _ ≤ u.val + 1 := by omega)
    (by
      calc
        u.val + 1 = u.val / N * N + (u.val % N + 1) := by omega
        _ = u.val / N * N + N := by rw [hrem]
        _ = (u.val / N + 1) * N := by simp [Nat.succ_mul]
        _ < (u.val / N + 2) * N := by
          exact (Nat.mul_lt_mul_right hN).2 (by omega))

theorem alphaStageIndex_block_mul
    {p N : ℕ} (hN : 0 < N) {i : Fin p} :
    alphaStageIndex (⟨i.val * N, by
      exact Nat.mul_lt_mul_of_pos_right i.isLt hN⟩ : Fin (p * N)) = i := by
  apply Fin.ext
  unfold alphaStageIndex
  exact Nat.mul_div_left i.val hN

theorem alphaStageIndex_at_offset
    {p N : ℕ} (hN : 0 < N) {i : Fin p} {k : Fin N} :
    alphaStageIndex (⟨i.val * N + k.val, by
      have hi := i.isLt
      have hk := k.isLt
      have hstep : i.val * N + k.val < (i.val + 1) * N := by
        calc
          i.val * N + k.val < i.val * N + N := Nat.add_lt_add_left hk _
          _ = (i.val + 1) * N := by simp [Nat.succ_mul]
      have hnext : (i.val + 1) * N ≤ p * N :=
        Nat.mul_le_mul_right N (Nat.succ_le_of_lt hi)
      omega⟩ : Fin (p * N)) = i := by
  apply Fin.ext
  change (i.val * N + k.val) / N = i.val
  have hdiv : (k.val + N * i.val) / N = k.val / N + i.val :=
    Nat.add_mul_div_left k.val i.val hN
  have hkdiv : k.val / N = 0 := Nat.div_eq_of_lt k.isLt
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, hkdiv] using hdiv

theorem alphaStageRemainder_at_offset
    {p N : ℕ} {i : Fin p} {k : Fin N} :
    (i.val * N + k.val) % N = k.val := by
  have hmod := Nat.add_mul_mod_self_left k.val N i.val
  have hkmod : k.val % N = k.val := Nat.mod_eq_of_lt k.isLt
  calc
    (i.val * N + k.val) % N = (k.val + N * i.val) % N := by
      rw [Nat.add_comm, Nat.mul_comm]
    _ = k.val % N := hmod
    _ = k.val := hkmod

theorem alphaStageRemainder_succ_same_block
    {p N : ℕ} (hN : 0 < N) {u : Fin (p * N)}
    (hrem : u.val % N + 1 < N) :
    (u.val + 1) % N = u.val % N + 1 := by
  have hdecomp : u.val / N * N + u.val % N = u.val := by
    simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
  have hdecomp' : u.val = u.val % N + N * (u.val / N) := by
    calc
      u.val = u.val / N * N + u.val % N := hdecomp.symm
      _ = u.val % N + N * (u.val / N) := by ac_rfl
  have hu : u.val + 1 = u.val % N + 1 + N * (u.val / N) := by
    omega
  calc
    (u.val + 1) % N = (u.val % N + 1 + N * (u.val / N)) % N := by rw [hu]
    _ = (u.val % N + 1) % N := Nat.add_mul_mod_self_left _ _ _
    _ = u.val % N + 1 := Nat.mod_eq_of_lt hrem

theorem alphaStageRemainder_succ_boundary
    {p N : ℕ} (hN : 0 < N) {u : Fin (p * N)}
    (hrem : u.val % N + 1 = N) :
    (u.val + 1) % N = 0 := by
  have hdecomp : u.val / N * N + u.val % N = u.val := by
    simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
  have hdecomp' : u.val = u.val % N + N * (u.val / N) := by
    calc
      u.val = u.val / N * N + u.val % N := hdecomp.symm
      _ = u.val % N + N * (u.val / N) := by ac_rfl
  have hu : u.val + 1 = u.val % N + 1 + N * (u.val / N) := by
    omega
  calc
    (u.val + 1) % N = (u.val % N + 1 + N * (u.val / N)) % N := by rw [hu]
    _ = (u.val % N + 1) % N := Nat.add_mul_mod_self_left _ _ _
    _ = N % N := by rw [hrem]
    _ = 0 := Nat.mod_self _

def alphaTableauPosition
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (s : Fin (finiteFactorStageCount p 0 N + 1)) : Fin (N + 1) := by
  by_cases hN0 : N = 0
  · exact boundary
  · by_cases hs : s.val < p * N
    · let u : Fin (p * N) := ⟨s.val, by simpa [finiteFactorStageCount] using hs⟩
      let k : Fin (N + 1) :=
        ⟨s.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hN0))⟩
      exact alphaRowBlockPosition T a boundary hbound (alphaStageIndex u) k
    · exact alphaRowBoundaryPosition T a boundary hbound (Fin.last p)

@[simp]
theorem alphaTableauPosition_of_internal
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (s : Fin (finiteFactorStageCount p 0 N + 1)) (hN0 : N ≠ 0)
    (hs : s.val < p * N) :
    alphaTableauPosition T a boundary hbound s =
      alphaRowBlockPosition T a boundary hbound
        (alphaStageIndex (⟨s.val, by simpa [finiteFactorStageCount] using hs⟩ : Fin (p * N)))
        ⟨s.val % N, Nat.lt_succ_of_lt (Nat.mod_lt _ (Nat.pos_of_ne_zero hN0))⟩ := by
  unfold alphaTableauPosition
  simp only [hN0, ↓reduceDIte, hs]

@[simp]
theorem alphaTableauPosition_of_terminal
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (s : Fin (finiteFactorStageCount p 0 N + 1)) (hN0 : N ≠ 0)
    (hs : ¬s.val < p * N) :
    alphaTableauPosition T a boundary hbound s =
      alphaRowBoundaryPosition T a boundary hbound (Fin.last p) := by
  unfold alphaTableauPosition
  simp only [hN0, ↓reduceDIte, hs]

@[simp]
theorem alphaTableauPosition_last
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hN0 : N ≠ 0) :
    alphaTableauPosition T a boundary hbound
        (Fin.last (finiteFactorStageCount p 0 N)) =
      alphaRowBoundaryPosition T a boundary hbound (Fin.last p) := by
  apply alphaTableauPosition_of_terminal T a boundary hbound _ hN0
  simp only [Fin.last, finiteFactorStageCount, Fin.val_mk, Nat.zero_add]
  exact Nat.lt_irrefl _

@[simp]
theorem alphaTableauPosition_at_block_boundary
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hN : 0 < N) (i : Fin p) :
    alphaTableauPosition T a boundary hbound
        (⟨i.val * N, by
          simp only [finiteFactorStageCount]
          simpa only [Nat.zero_add] using
            (Nat.lt_succ_of_lt (Nat.mul_lt_mul_of_pos_right i.isLt hN))⟩ :
          Fin (finiteFactorStageCount p 0 N + 1)) =
      alphaRowBlockSource T a boundary hbound i := by
  have hs : i.val * N < p * N := Nat.mul_lt_mul_of_pos_right i.isLt hN
  rw [alphaTableauPosition_of_internal T a boundary hbound _ hN.ne' (by
    simpa [finiteFactorStageCount] using hs)]
  have hi := alphaStageIndex_block_mul (p := p) (N := N) hN (i := i)
  have hzero : i.val * N % N = 0 := Nat.mul_mod_left _ _
  have hk :
      (⟨i.val * N % N, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1)) =
        (0 : Fin (N + 1)) := by
    apply Fin.ext
    exact hzero
  simpa [hi, hk] using alphaRowBlockPosition_zero T a boundary hbound i

@[simp]
theorem alphaTableauPosition_at_block_offset
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hN : 0 < N) (i : Fin p) (k : Fin N) :
    alphaTableauPosition T a boundary hbound
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
          simpa only [Nat.zero_add] using
            Nat.lt_succ_of_le (hstep.le.trans hnext)⟩ :
          Fin (finiteFactorStageCount p 0 N + 1)) =
      alphaRowBlockPosition T a boundary hbound i
        ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
  have hs : i.val * N + k.val < p * N := by
    have hi := i.isLt
    have hk := k.isLt
    have hstep : i.val * N + k.val < (i.val + 1) * N := by
      calc
        i.val * N + k.val < i.val * N + N := Nat.add_lt_add_left hk _
        _ = (i.val + 1) * N := by simp [Nat.succ_mul]
    have hnext : (i.val + 1) * N ≤ p * N :=
      Nat.mul_le_mul_right N (Nat.succ_le_of_lt hi)
    exact hstep.trans_le (by simpa only [Nat.zero_add] using hnext)
  rw [alphaTableauPosition_of_internal T a boundary hbound _ hN.ne'
    (by simpa [finiteFactorStageCount] using hs)]
  have hi := alphaStageIndex_at_offset hN (p := p) (N := N) (i := i) (k := k)
  have hk := alphaStageRemainder_at_offset (i := i) (k := k)
  have hk0 : k.val % N = k.val := Nat.mod_eq_of_lt k.isLt
  have hk' :
      (⟨(i.val * N + k.val) % N,
        Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩ : Fin (N + 1)) =
        (⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ : Fin (N + 1)) := by
    apply Fin.ext
    exact hk
  simpa [hi, hk', hk0]

theorem alphaTableauPosition_network_step
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hp : 0 < p) (t : Fin (finiteFactorStageCount p 0 N)) :
    NetworkStepAllowed p 0 N t.val
      (alphaTableauPosition T a boundary hbound t.castSucc)
      (alphaTableauPosition T a boundary hbound t.succ) := by
  by_cases hN0 : N = 0
  · subst N
    have ht := t.isLt
    simp [finiteFactorStageCount] at ht
  have hN : 0 < N := Nat.pos_of_ne_zero hN0
  let u : Fin (p * N) := ⟨t.val, by
    simpa [finiteFactorStageCount] using t.isLt⟩
  let i : Fin p := alphaStageIndex u
  let k : Fin N := ⟨t.val % N, Nat.mod_lt _ hN⟩
  have hdecomp : i.val * N + k.val = t.val := by
    simpa [i, k, u] using alphaStageIndex_mul_add_mod hN u
  have hpos_cur :
      alphaTableauPosition T a boundary hbound t.castSucc =
        alphaRowBlockPosition T a boundary hbound i
          ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩ := by
    have hstage : t.castSucc =
        (⟨i.val * N + k.val, by
          simp only [finiteFactorStageCount]
          exact Nat.lt_succ_of_le (hdecomp.le.trans t.isLt.le)⟩ :
          Fin (finiteFactorStageCount p 0 N + 1)) := by
      apply Fin.ext
      exact hdecomp.symm
    rw [hstage]
    exact alphaTableauPosition_at_block_offset T a boundary hbound hN i k
  by_cases hsame : k.val + 1 < N
  · let kNext : Fin N := ⟨k.val + 1, hsame⟩
    have hnext_internal : t.val + 1 < p * N := by
      have hdecomp' : u.val / N * N + u.val % N = u.val := by
        simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
      dsimp [u] at hdecomp'
      have hqbound : u.val / N < p := (alphaStageIndex u).isLt
      have hsame' : u.val % N + 1 < N := by simpa [u, k] using hsame
      calc
        t.val + 1 = u.val / N * N + (u.val % N + 1) := by
          dsimp [u]
          omega
        _ < u.val / N * N + N := Nat.add_lt_add_left hsame' _
        _ = (u.val / N + 1) * N := by simp [Nat.succ_mul]
        _ ≤ p * N := Nat.mul_le_mul_right N (Nat.succ_le_of_lt hqbound)
    have hindexNext :
        alphaStageIndex (⟨u.val + 1, hnext_internal⟩ : Fin (p * N)) = i := by
      exact alphaStageIndex_succ_same_block hN (u := u) (by simpa [u, k] using hsame)
    have hnextval : i.val * N + kNext.val = t.val + 1 := by
      dsimp [kNext]
      omega
    have htle : t.val + 1 ≤ p * N := by
      simpa [finiteFactorStageCount] using (Nat.succ_le_of_lt t.isLt)
    have hstage_next : t.succ =
        (⟨i.val * N + kNext.val, by
          simp only [finiteFactorStageCount]
          exact Nat.lt_succ_of_le (hnextval.le.trans
            (by simpa only [Nat.zero_add] using htle))⟩ :
          Fin (finiteFactorStageCount p 0 N + 1)) := by
      apply Fin.ext
      exact hnextval.symm
    have hpos_next :
        alphaTableauPosition T a boundary hbound t.succ =
          alphaRowBlockPosition T a boundary hbound i
            ⟨kNext.val, Nat.lt_succ_of_lt kNext.isLt⟩ := by
      rw [hstage_next]
      exact alphaTableauPosition_at_block_offset T a boundary hbound hN i kNext
    have hlocal := alphaRowBlockPosition_network_step T a boundary hbound i k
    unfold NetworkStepAllowed at hlocal ⊢
    rw [if_neg (by omega : ¬k.val < 0)] at hlocal
    rw [if_neg (by omega : ¬t.val < 0)]
    rw [hpos_cur, hpos_next]
    rcases hlocal with hstay | hmove
    · exact Or.inl hstay
    · rcases hmove with ⟨_, hx, hy⟩
      right
      refine ⟨i.isLt, ?_, hy⟩
      simpa [k, u] using hx
  · have hboundary : k.val + 1 = N := by omega
    by_cases hfinal : t.val + 1 = p * N
    · have hstage_next : t.succ =
          Fin.last (finiteFactorStageCount p 0 N) := by
        apply Fin.ext
        simpa [finiteFactorStageCount] using hfinal
      have hpos_next :
          alphaTableauPosition T a boundary hbound t.succ =
            alphaRowBlockPosition T a boundary hbound i k.succ := by
        rw [hstage_next]
        rw [alphaTableauPosition_last T a boundary hbound hN0]
        have hindexlast : i.val + 1 = p := by
          have hdecomp' : u.val / N * N + u.val % N = u.val := by
            simpa [Nat.mul_comm] using Nat.div_add_mod u.val N
          have heq : (i.val + 1) * N = p * N := by
            calc
              (i.val + 1) * N = i.val * N + N := by simp [Nat.succ_mul]
              _ = t.val + 1 := by
                dsimp [k] at hboundary
                omega
              _ = p * N := hfinal
          exact Nat.eq_of_mul_eq_mul_right hN heq
        have hprefixlast := alphaRowPrefixCount_add_blockCount_last T a i hindexlast
        rw [alphaRowBoundaryPosition_last]
        have hkLast : k.succ = Fin.last N := by
          apply Fin.ext
          change k.val + 1 = N
          exact hboundary
        rw [hkLast, alphaRowBlockPosition_last]
        apply Fin.ext
        unfold alphaRowBlockSource
        change boundary.val + S.rowWidth a =
          boundary.val + alphaRowPrefixCount T a i + alphaRowBlockCount T a i
        omega
      have hlocal := alphaRowBlockPosition_network_step T a boundary hbound i k
      unfold NetworkStepAllowed at hlocal ⊢
      rw [if_neg (by omega : ¬k.val < 0)] at hlocal
      rw [if_neg (by omega : ¬t.val < 0)]
      rw [hpos_cur, hpos_next]
      rcases hlocal with hstay | hmove
      · exact Or.inl hstay
      · rcases hmove with ⟨_, hx, hy⟩
        right
        refine ⟨i.isLt, ?_, hy⟩
        simpa [k, u] using hx
    · have hnext_le : t.val + 1 ≤ p * N := by
        simpa [finiteFactorStageCount] using (Nat.succ_le_of_lt t.isLt)
      have hnext_internal : t.val + 1 < p * N :=
        Nat.lt_of_le_of_ne hnext_le hfinal
      let iNext : Fin p := ⟨i.val + 1, by
        have hq := i.isLt
        have heq : (i.val + 1) * N = t.val + 1 := by
          calc
            (i.val + 1) * N = i.val * N + N := by simp [Nat.succ_mul]
            _ = t.val + 1 := by
              dsimp [k] at hboundary
              omega
        by_contra hnot
        have hge : p ≤ i.val + 1 := Nat.le_of_not_gt hnot
        have hmul := Nat.mul_le_mul_right N hge
        omega⟩
      have hindexNext :
          alphaStageIndex (⟨u.val + 1, hnext_internal⟩ : Fin (p * N)) = iNext := by
        apply alphaStageIndex_succ_next_block hN (u := u)
        · simpa [u, k] using hboundary
      have hnextval : iNext.val * N = t.val + 1 := by
        change (i.val + 1) * N = t.val + 1
        calc
          (i.val + 1) * N = i.val * N + N := by simp [Nat.succ_mul]
          _ = i.val * N + (k.val + 1) := by rw [hboundary]
          _ = t.val + 1 := by omega
      have hstage_next : t.succ =
          (⟨iNext.val * N, by
            simp only [finiteFactorStageCount]
            exact Nat.lt_succ_of_le (hnextval.le.trans
              (by simpa only [Nat.zero_add] using hnext_le))⟩ :
          Fin (finiteFactorStageCount p 0 N + 1)) := by
        apply Fin.ext
        exact hnextval.symm
      have hpos_next :
          alphaTableauPosition T a boundary hbound t.succ =
            alphaRowBlockPosition T a boundary hbound i k.succ := by
        rw [hstage_next]
        rw [alphaTableauPosition_at_block_boundary T a boundary hbound hN iNext]
        rw [alphaRowBlockSource_succ T a boundary hbound i
          (by exact iNext.isLt)]
        have hkLast : k.succ = Fin.last N := by
          apply Fin.ext
          change k.val + 1 = N
          exact hboundary
        rw [hkLast, alphaRowBlockPosition_last]
      have hlocal := alphaRowBlockPosition_network_step T a boundary hbound i k
      unfold NetworkStepAllowed at hlocal ⊢
      rw [if_neg (by omega : ¬k.val < 0)] at hlocal
      rw [if_neg (by omega : ¬t.val < 0)]
      rw [hpos_cur, hpos_next]
      rcases hlocal with hstay | hmove
      · exact Or.inl hstay
      · rcases hmove with ⟨_, hx, hy⟩
        right
        refine ⟨i.isLt, ?_, hy⟩
        simpa [k, u] using hx

theorem alphaTableauPosition_zero
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hp : 0 < p) :
    alphaTableauPosition T a boundary hbound 0 = boundary := by
  by_cases hN0 : N = 0
  · subst N
    rfl
  have hN : 0 < N := Nat.pos_of_ne_zero hN0
  let i0 : Fin p := ⟨0, hp⟩
  let k0 : Fin N := ⟨0, hN⟩
  have hpos := alphaTableauPosition_at_block_offset T a boundary hbound hN i0 k0
  have hzero :
      (⟨i0.val * N + k0.val, by
        simp only [finiteFactorStageCount]
        have hstep : i0.val * N + k0.val < (i0.val + 1) * N := by
          calc
            i0.val * N + k0.val < i0.val * N + N := Nat.add_lt_add_left k0.isLt _
            _ = (i0.val + 1) * N := by simp [Nat.succ_mul]
        have hnext : (i0.val + 1) * N ≤ p * N :=
          Nat.mul_le_mul_right N (Nat.succ_le_of_lt i0.isLt)
        simpa only [Nat.zero_add] using Nat.lt_succ_of_le (hstep.le.trans hnext)⟩ :
        Fin (finiteFactorStageCount p 0 N + 1)) = (0 : Fin (finiteFactorStageCount p 0 N + 1)) := by
    apply Fin.ext
    simp [i0, k0]
  have hpos0 :
      alphaTableauPosition T a boundary hbound 0 =
        alphaRowBlockPosition T a boundary hbound i0
          ⟨k0.val, Nat.lt_succ_of_lt k0.isLt⟩ := by
    simpa [hzero] using hpos
  have hk0' :
      (⟨k0.val, Nat.lt_succ_of_lt k0.isLt⟩ : Fin (N + 1)) = 0 := by
    apply Fin.ext
    simp [k0]
  rw [hk0', alphaRowBlockPosition_zero] at hpos0
  apply Fin.ext
  calc
    (alphaTableauPosition T a boundary hbound 0).val =
        (alphaRowBlockSource T a boundary hbound i0).val := congrArg Fin.val hpos0
    _ = boundary.val := by
      unfold alphaRowBlockSource
      change boundary.val + alphaRowPrefixCount T a i0 = boundary.val
      rw [alphaRowPrefixCount_zero T a hp]
      simp

theorem alphaTableauPosition_sink
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hp : 0 < p) :
    alphaTableauPosition T a boundary hbound
        (Fin.last (finiteFactorStageCount p 0 N)) =
      ⟨boundary.val + S.rowWidth a, by omega⟩ := by
  by_cases hN0 : N = 0
  · subst N
    apply Fin.ext
    have h := hbound
    simp at h
    omega
  rw [alphaTableauPosition_last T a boundary hbound hN0]
  exact alphaRowBoundaryPosition_last T a boundary hbound

theorem tupleCoproductTableau_middle_eq_outer_q_zero
    {p r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct) :
    T.intermediate.middle = containingOuterPartition J := by
  apply RectanglePartition.rowLength_injective
  funext a
  apply Fin.ext
  have hfit := T.tableaux.betaTableau.fitsRowBound a
  have hwidth : T.intermediate.betaShape.rowWidth a = 0 :=
    Nat.eq_zero_of_le_zero hfit
  have hwidthNat : containingOuterPartition J a - T.intermediate.middle a = 0 := by
    simpa [IntermediateRectanglePartition.betaShape,
      FiniteSkewShape.rowWidth_eq_sub] using hwidth
  have hle : T.intermediate.middle a ≤ containingOuterPartition J a :=
    T.intermediate.outer_ge a
  have hge : containingOuterPartition J a ≤ T.intermediate.middle a :=
    Nat.sub_eq_zero_iff_le.mp hwidthNat
  exact Nat.le_antisymm hle hge

theorem tupleCoproductTableau_alpha_row_bound_q_zero
    {p r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (a : Fin r) :
    (tupleNetworkSource J a).val +
        T.intermediate.alphaShape.rowWidth a ≤ tupleNetworkBound J := by
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  rw [FiniteSkewShape.rowWidth_eq_sub]
  change (tupleNetworkSource J a).val +
      (T.intermediate.middle a - T.intermediate.alphaShape.inner a) ≤ J.tupleWidth
  rw [hmid]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - I.associatedPart a) ≤ J.tupleWidth
  have hJ := J.value_le_tupleWidth a.rev
  have hI := (hstruct a.rev).trans hJ
  have hJpos := J.position_le a.rev
  have hIpos := I.position_le a.rev
  change (J.tupleWidth - (J a.rev - 1)) +
      (J a.rev - (a.rev.val + 1) - (I a.rev - (a.rev.val + 1))) ≤ J.tupleWidth
  omega

theorem tupleCoproductTableau_alpha_row_endpoint_q_zero
    {p r : ℕ} {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (a : Fin r) :
    (tupleNetworkSource J a).val +
        T.intermediate.alphaShape.rowWidth a =
      (tupleNetworkSink I J hstruct a).val := by
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  rw [FiniteSkewShape.rowWidth_eq_sub]
  change (tupleNetworkSource J a).val +
      (T.intermediate.middle a - T.intermediate.alphaShape.inner a) =
        (tupleNetworkSink I J hstruct a).val
  rw [hmid]
  change (J.tupleWidth - (J a.rev - 1)) +
      (J.associatedPart a - I.associatedPart a) =
        J.tupleWidth - (I a.rev - 1)
  have hassoc : J.associatedPart a - I.associatedPart a =
      J a.rev - I a.rev := by
    change J a.rev - (a.rev.val + 1) -
      (I a.rev - (a.rev.val + 1)) = J a.rev - I a.rev
    have hIpos := I.position_le a.rev
    have hJpos := J.position_le a.rev
    have hstruct' := hstruct a.rev
    omega
  rw [hassoc]
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

noncomputable def alphaTableauPath
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (D : FiniteEdreiData p 0) (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (hp : 0 < p) :
    FiniteFactorPath D N boundary
      (⟨boundary.val + S.rowWidth a, by omega⟩ : Fin (N + 1)) :=
  { position := alphaTableauPosition T a boundary hbound
    source_eq := alphaTableauPosition_zero T a boundary hbound hp
    sink_eq := by
      simpa [finiteFactorStageCount] using alphaTableauPosition_sink T a boundary hbound hp
    valid := alphaTableauPosition_network_step T a boundary hbound hp }

noncomputable def tupleAlphaTableauPath
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r) :
    FiniteFactorPath (reverseFiniteEdreiData D) (tupleNetworkBound J)
      (tupleNetworkSource J a) (tupleNetworkSink I J hstruct a) := by
  have hbound := tupleCoproductTableau_alpha_row_bound_q_zero T a
  let P := alphaTableauPath (reverseFiniteEdreiData D)
    T.tableaux.alphaTableau a (tupleNetworkSource J a) hbound hp
  refine
    { position := P.position
      source_eq := P.source_eq
      sink_eq := ?_
      valid := P.valid }
  rw [P.sink_eq]
  apply Fin.ext
  exact tupleCoproductTableau_alpha_row_endpoint_q_zero T a

@[simp]
theorem tupleAlphaTableauPath_position
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (s : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) :
    (tupleAlphaTableauPath D I J hstruct T hp a).position s =
      alphaTableauPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
        (tupleCoproductTableau_alpha_row_bound_q_zero T a) s :=
  rfl

theorem alphaCellCrossingStage_eq_of_entry_eq_q_zero
    {p r : ℕ} {D : FiniteEdreiData p 0}
    {I J : IncreasingIndexTuple r}
    {hstruct : StructurallyAdmissible I J}
    (F G : TupleVertexDisjointPathFamily D I J hstruct)
    (xF : (F.intermediate.alphaShape).Cell)
    (xG : (G.intermediate.alphaShape).Cell)
    (hval : xF.val = xG.val)
    (hentry : alphaCellEntry F xF = alphaCellEntry G xG) :
    alphaCellCrossingStage F xF = alphaCellCrossingStage G xG := by
  have hblock :
      (alphaCellCrossingStage F xF).val =
          (alphaCellCrossingStage G xG).val := by
    have hrev := Fin.rev_injective hentry
    have hquot :
        ((alphaCellCrossingStage F xF).val / J.tupleWidth) =
          ((alphaCellCrossingStage G xG).val / J.tupleWidth) := by
      simpa [alphaCellEntry, Nat.sub_zero] using congrArg Fin.val hrev
    have hdecompF := alphaCellCrossingStage_decomposition F xF
    have hdecompG := alphaCellCrossingStage_decomposition G xG
    have hwire :
        (alphaCellCrossingWire F xF).val =
          (alphaCellCrossingWire G xG).val := by
      rw [alphaCellCrossingWire_val, alphaCellCrossingWire_val]
      simpa [hval]
    have hquot' :
        (alphaCellCrossingStage F xF).val / J.tupleWidth =
          (alphaCellCrossingStage G xG).val / J.tupleWidth := by
      exact congrArg Fin.val hrev
    have hdecompF' :
        (alphaCellCrossingStage F xF).val =
          ((alphaCellCrossingStage F xF).val / J.tupleWidth) * J.tupleWidth +
            (alphaCellCrossingWire F xF).val := by
      simpa [Nat.sub_zero, Nat.zero_add] using hdecompF
    have hdecompG' :
        (alphaCellCrossingStage G xG).val =
          ((alphaCellCrossingStage G xG).val / J.tupleWidth) * J.tupleWidth +
            (alphaCellCrossingWire G xG).val := by
      simpa [Nat.sub_zero, Nat.zero_add] using hdecompG
    rw [← hquot'] at hdecompG'
    rw [← hwire] at hdecompG'
    exact hdecompF'.trans hdecompG'.symm
  apply Fin.ext
  exact hblock

theorem canonicalGoodTableauMap_injective_p_pos_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hp : 0 < p)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    Function.Injective (@canonicalGoodTableauMap p 0 r D I J hstruct) := by
  intro F G hT
  have hpermF := tupleNetwork_good_perm_eq_refl F.1 F.2
  have hpermG := tupleNetwork_good_perm_eq_refl G.1 G.2
  apply Subtype.ext
  apply networkTerm_ext
  · rw [hpermF, hpermG]
  · intro a s
    have hI := tupleCoproductTableauOfPathFamily_intermediate_injective F G hT
    have hFmid : (TupleVertexDisjointPathFamily.intermediate F).middle =
        containingOuterPartition J := by
      have h := tupleCoproductTableau_middle_eq_outer_q_zero
        (tupleCoproductTableauOfPathFamily F)
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using h
    have hGmid : (TupleVertexDisjointPathFamily.intermediate G).middle =
        containingOuterPartition J := by
      have h := tupleCoproductTableau_middle_eq_outer_q_zero
        (tupleCoproductTableauOfPathFamily G)
      simpa only [tupleCoproductTableauOfPathFamily_intermediate] using h
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
      let cval := J.tupleWidth - (a.rev.val + k + 1)
      have hcN : cval < J.tupleWidth := by
        change J.tupleWidth - (a.rev.val + k + 1) < J.tupleWidth
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        have hJ := J.value_le_tupleWidth a.rev
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by
          change k < J.tupleWidth - (I a.rev - 1) at hsink
          have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
          omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      let c : Fin J.tupleWidth := ⟨cval, hcN⟩
      have hcellF :
          (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate F).alphaShape.cells := by
        apply FiniteSkewShape.mem_cells.mpr
        change containedInnerPartition I J hstruct a ≤ cval ∧
          cval < (TupleVertexDisjointPathFamily.intermediate F).middle a
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
          (a, c) ∈ (TupleVertexDisjointPathFamily.intermediate G).alphaShape.cells := by
        apply FiniteSkewShape.mem_cells.mpr
        change containedInnerPartition I J hstruct a ≤ cval ∧
          cval < (TupleVertexDisjointPathFamily.intermediate G).middle a
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
      let xF : (TupleVertexDisjointPathFamily.intermediate F).alphaShape.Cell :=
        ⟨(a, c), hcellF⟩
      let xG : (TupleVertexDisjointPathFamily.intermediate G).alphaShape.Cell :=
        ⟨(a, c), hcellG⟩
      have hwireF : (alphaCellCrossingWire F xF).val = k := by
        rw [alphaCellCrossingWire_val]
        change J.tupleWidth - (a.rev.val +
          (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      have hwireG : (alphaCellCrossingWire G xG).val = k := by
        rw [alphaCellCrossingWire_val]
        change J.tupleWidth - (a.rev.val +
          (J.tupleWidth - (a.rev.val + k + 1) + 1)) = k
        have hIpos := I.position_le a.rev
        have hJpos := J.position_le a.rev
        change k < J.tupleWidth - (I a.rev - 1) at hsink
        have hIbound := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
        have hsum : a.rev.val + k + 1 ≤ J.tupleWidth := by omega
        have hsub := Nat.sub_add_cancel hsum
        omega
      have hentry := tupleCoproductTableauOfPathFamily_alpha_entry_injective F G hT xF
      have hentry' : alphaCellEntry F xF = alphaCellEntry G xG := by
        simpa [xF, xG, hI] using hentry
      have hstage : alphaCellCrossingStage F xF =
          alphaCellCrossingStage G xG := by
        apply alphaCellCrossingStage_eq_of_entry_eq_q_zero F G xF xG
        · rfl
        · exact hentry'
      have hPFstage : alphaCellCrossingStage F xF =
          PF.crossingStage k hsource hsink := by
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
      have hPGstage : alphaCellCrossingStage G xG =
          PG.crossingStage k hsource hsink := by
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
      calc
        PF.crossingStage k hsource hsink = alphaCellCrossingStage F xF := hPFstage.symm
        _ = alphaCellCrossingStage G xG := hstage
        _ = PG.crossingStage k hsource hsink := hPGstage
    have hpath := FiniteFactorPath.ext_of_crossingStage_eq PF PG hcross
    have hpos := congrArg (fun P => P.position s) hpath
    simpa [PF, PG] using hpos

theorem alphaRowPrefixCount_le_of_row_lt
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) {a b : Fin r} (hab : a < b) (i : Fin p) :
    alphaRowPrefixCount T a i ≤
      alphaRowPrefixCount T b i + (S.outer a - S.outer b) := by
  let Ua : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c < i
  let Ub : Finset (AlphaRowCell T b) :=
    Finset.univ.filter fun c => alphaRowBlock T b c < i
  let UL : Finset (AlphaRowCell T a) :=
    Ua.filter fun c => c.val.val < S.outer b
  let UR : Finset (AlphaRowCell T a) :=
    Ua.filter fun c => S.outer b ≤ c.val.val
  have hdisj : Disjoint UL UR := by
    rw [Finset.disjoint_left]
    intro c hcL hcR
    exact (Nat.not_le_of_lt (Finset.mem_filter.mp hcL).2)
      (Finset.mem_filter.mp hcR).2
  have hU : Ua = UL ∪ UR := by
    ext c
    simp only [Ua, UL, UR, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hmap : ∀ (c : AlphaRowCell T a) (hc : c ∈ UL),
      (⟨c.val, by
        have hcRow := c.property
        have hinner := S.inner.antitone (show a ≤ b by omega)
        change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
        have houter := (Finset.mem_filter.mp hc).2
        have hcinner := (FiniteSkewShape.mem_rowCells.mp hcRow).1
        apply FiniteSkewShape.mem_rowCells.mpr
        change (S.inner b : ℕ) ≤ c.val.val ∧ c.val.val < (S.outer b : ℕ)
        exact ⟨by omega, houter⟩⟩ :
        AlphaRowCell T b) ∈ Ub := by
    intro c hc
    let d : AlphaRowCell T b := ⟨c.val, by
      have hcell := c.property
      have hinner := S.inner.antitone (show a ≤ b by omega)
      change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
      have houter := (Finset.mem_filter.mp hc).2
      have hcellinner := (FiniteSkewShape.mem_rowCells.mp hcell).1
      apply FiniteSkewShape.mem_rowCells.mpr
      change (S.inner b : ℕ) ≤ c.val.val ∧ c.val.val < (S.outer b : ℕ)
      exact ⟨by omega, houter⟩⟩
    have hca : alphaRowBlock T a c < i :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    have hentry := T.column_strict
      (x := ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩)
      (y := ⟨(b, c.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩)
      rfl hab
    have hblock : alphaRowBlock T b d < alphaRowBlock T a c := by
      unfold alphaRowBlock
      apply Fin.rev_lt_rev.mpr
      exact hentry
    change d ∈ Ub
    simp only [Ub, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hblock.trans hca
  let f : {c : AlphaRowCell T a // c ∈ UL} → AlphaRowCell T b := fun c =>
    ⟨c.val.val, by
      have hc := c.val.property
      have hinner := S.inner.antitone (show a ≤ b by omega)
      change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
      have houter := (Finset.mem_filter.mp c.property).2
      have hcinner := (FiniteSkewShape.mem_rowCells.mp hc).1
      apply FiniteSkewShape.mem_rowCells.mpr
      change (S.inner b : ℕ) ≤ c.val.val.val ∧ c.val.val.val < (S.outer b : ℕ)
      exact ⟨by omega, houter⟩⟩
  have hf_inj : Function.Injective f := by
    intro c d hfd
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : AlphaRowCell T b => z.val.val) hfd
  have hf_inj' : Set.InjOn f (↑UL.attach : Set {c : AlphaRowCell T a // c ∈ UL}) := by
    intro c hc d hd h
    exact hf_inj h
  let V := UL.attach.image f
  have himage : V ⊆ Ub := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
    exact hmap c.val c.property
  have hcardL : UL.card ≤ Ub.card := by
    have hcardImage := Finset.card_le_card himage
    have hcardEq : V.card = UL.card := by
      dsimp [V]
      rw [Finset.card_image_iff.mpr hf_inj']
      simp
    rw [hcardEq] at hcardImage
    exact hcardImage
  let W : Finset ℕ := UR.image (fun c => c.val.val)
  have hW_inj : Set.InjOn (fun c : AlphaRowCell T a => c.val.val) UR := by
    intro c hc d hd hcd
    apply Subtype.ext
    apply Fin.ext
    exact hcd
  have hWsub : W ⊆ Finset.Ico (S.outer b) (S.outer a) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
    have hcU := (Finset.mem_filter.mp hc).1
    have hcR := (Finset.mem_filter.mp hc).2
    have houter := (FiniteSkewShape.mem_rowCells.mp c.property).2
    exact Finset.mem_Ico.mpr ⟨hcR, houter⟩
  have hcardR : UR.card ≤ S.outer a - S.outer b := by
    have hcardImage := Finset.card_le_card hWsub
    have hcardEq : W.card = UR.card := by
      dsimp [W]
      rw [Finset.card_image_iff.mpr hW_inj]
    rw [hcardEq, Nat.card_Ico] at hcardImage
    exact hcardImage
  have hcardU : Ua.card = UL.card + UR.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj]
  have hprefixA : Ua.card = alphaRowPrefixCount T a i := rfl
  have hprefixB : Ub.card = alphaRowPrefixCount T b i := rfl
  rw [← hprefixA, ← hprefixB, hcardU]
  omega

/-- Cells in an earlier row whose block is at most `i` inject into the prefix of a later row. -/
theorem alphaRowPrefixCount_add_blockCount_le_of_row_lt
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) {a b : Fin r} (hab : a < b) (i : Fin p) :
    alphaRowPrefixCount T a i + alphaRowBlockCount T a i ≤
      alphaRowPrefixCount T b i + (S.outer a - S.outer b) := by
  let Ua : Finset (AlphaRowCell T a) :=
    Finset.univ.filter fun c => alphaRowBlock T a c ≤ i
  let Ub : Finset (AlphaRowCell T b) :=
    Finset.univ.filter fun c => alphaRowBlock T b c < i
  let UL : Finset (AlphaRowCell T a) :=
    Ua.filter fun c => c.val.val < S.outer b
  let UR : Finset (AlphaRowCell T a) :=
    Ua.filter fun c => S.outer b ≤ c.val.val
  have hdisj : Disjoint UL UR := by
    rw [Finset.disjoint_left]
    intro c hcL hcR
    exact (Nat.not_le_of_lt (Finset.mem_filter.mp hcL).2)
      (Finset.mem_filter.mp hcR).2
  have hU : Ua = UL ∪ UR := by
    ext c
    simp only [Ua, UL, UR, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    omega
  have hmap : ∀ (c : AlphaRowCell T a) (hc : c ∈ UL),
      (⟨c.val, by
        have hcRow := c.property
        have hinner := S.inner.antitone (show a ≤ b by omega)
        change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
        have houter := (Finset.mem_filter.mp hc).2
        have hcinner := (FiniteSkewShape.mem_rowCells.mp hcRow).1
        apply FiniteSkewShape.mem_rowCells.mpr
        change (S.inner b : ℕ) ≤ c.val.val ∧ c.val.val < (S.outer b : ℕ)
        exact ⟨by omega, houter⟩⟩ :
        AlphaRowCell T b) ∈ Ub := by
    intro c hc
    let d : AlphaRowCell T b := ⟨c.val, by
      have hcell := c.property
      have hinner := S.inner.antitone (show a ≤ b by omega)
      change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
      have houter := (Finset.mem_filter.mp hc).2
      have hcellinner := (FiniteSkewShape.mem_rowCells.mp hcell).1
      apply FiniteSkewShape.mem_rowCells.mpr
      change (S.inner b : ℕ) ≤ c.val.val ∧ c.val.val < (S.outer b : ℕ)
      exact ⟨by omega, houter⟩⟩
    have hca : alphaRowBlock T a c ≤ i :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
    have hentry := T.column_strict
      (x := ⟨(a, c.val), by
        simpa [FiniteSkewShape.rowCells] using c.property⟩)
      (y := ⟨(b, c.val), by
        simpa [FiniteSkewShape.rowCells] using d.property⟩)
      rfl hab
    have hblock : alphaRowBlock T b d < alphaRowBlock T a c := by
      unfold alphaRowBlock
      apply Fin.rev_lt_rev.mpr
      exact hentry
    change d ∈ Ub
    simp only [Ub, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hblock.trans_le hca
  let f : {c : AlphaRowCell T a // c ∈ UL} → AlphaRowCell T b := fun c =>
    ⟨c.val.val, by
      have hc := c.val.property
      have hinner := S.inner.antitone (show a ≤ b by omega)
      change (S.inner b : ℕ) ≤ (S.inner a : ℕ) at hinner
      have houter := (Finset.mem_filter.mp c.property).2
      have hcinner := (FiniteSkewShape.mem_rowCells.mp hc).1
      apply FiniteSkewShape.mem_rowCells.mpr
      change (S.inner b : ℕ) ≤ c.val.val.val ∧ c.val.val.val < (S.outer b : ℕ)
      exact ⟨by omega, houter⟩⟩
  have hf_inj : Function.Injective f := by
    intro c d hfd
    apply Subtype.ext
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : AlphaRowCell T b => z.val.val) hfd
  have hf_inj' : Set.InjOn f (↑UL.attach : Set {c : AlphaRowCell T a // c ∈ UL}) := by
    intro c hc d hd h
    exact hf_inj h
  let V := UL.attach.image f
  have himage : V ⊆ Ub := by
    intro d hd
    rcases Finset.mem_image.mp hd with ⟨c, hc, rfl⟩
    exact hmap c.val c.property
  have hcardL : UL.card ≤ Ub.card := by
    have hcardImage := Finset.card_le_card himage
    have hcardEq : V.card = UL.card := by
      dsimp [V]
      rw [Finset.card_image_iff.mpr hf_inj']
      simp
    rw [hcardEq] at hcardImage
    exact hcardImage
  let W : Finset ℕ := UR.image (fun c => c.val.val)
  have hW_inj : Set.InjOn (fun c : AlphaRowCell T a => c.val.val) UR := by
    intro c hc d hd hcd
    apply Subtype.ext
    apply Fin.ext
    exact hcd
  have hWsub : W ⊆ Finset.Ico (S.outer b) (S.outer a) := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨c, hc, rfl⟩
    have hcR := (Finset.mem_filter.mp hc).2
    have houter := (FiniteSkewShape.mem_rowCells.mp c.property).2
    exact Finset.mem_Ico.mpr ⟨hcR, houter⟩
  have hcardR : UR.card ≤ S.outer a - S.outer b := by
    have hcardImage := Finset.card_le_card hWsub
    have hcardEq : W.card = UR.card := by
      dsimp [W]
      rw [Finset.card_image_iff.mpr hW_inj]
    rw [hcardEq, Nat.card_Ico] at hcardImage
    exact hcardImage
  have hcardU : Ua.card = UL.card + UR.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj]
  have hprefixA :
      alphaRowPrefixCount T a i + alphaRowBlockCount T a i = Ua.card := by
    simpa [Ua] using alphaRowPrefixCount_add_blockCount_eq_card_filter_le T a i
  have hprefixB : Ub.card = alphaRowPrefixCount T b i := rfl
  rw [hprefixA, ← hprefixB, hcardU]
  omega

theorem alphaRowBlockSource_add_tailCount_eq
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (c : AlphaRowCell T a) :
    boundary.val + alphaRowPrefixCount T a (alphaRowBlock T a c) +
        (Finset.univ.filter fun d : AlphaRowCell T a =>
          c.val.val < d.val.val ∧
            alphaRowBlock T a d = alphaRowBlock T a c).card =
      boundary.val + (S.outer a - (c.val.val + 1)) := by
  let i := alphaRowBlock T a c
  let U : Finset (AlphaRowCell T a) := Finset.univ.filter fun d =>
    c.val.val < d.val.val
  let V : Finset (AlphaRowCell T a) := Finset.univ.filter fun d =>
    alphaRowBlock T a d < i
  let R : Finset (AlphaRowCell T a) := Finset.univ.filter fun d =>
    c.val.val < d.val.val ∧ alphaRowBlock T a d = i
  have hc : alphaRowBlock T a c = i := rfl
  have hU : U = V ∪ R := by
    ext d
    simp only [U, V, R, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    constructor
    · intro hd
      have hle : alphaRowBlock T a d ≤ i := by
        apply alphaRowBlock_le_of_col_le T a
        exact Fin.mk_le_mk.mpr (Nat.le_of_lt hd)
      exact (lt_or_eq_of_le hle).elim Or.inl (fun heq => Or.inr ⟨hd, heq⟩)
    · intro hd
      rcases hd with hd | hd
      · have hnot : ¬d.val.val ≤ c.val.val := by
          intro hdc
          have hle : i ≤ alphaRowBlock T a d := by
            apply alphaRowBlock_le_of_col_le T a
            exact Fin.mk_le_mk.mpr hdc
          omega
        have hlt : c.val.val < d.val.val := by omega
        exact hlt
      · exact hd.1
  have hdisj : Disjoint V R := by
    rw [Finset.disjoint_left]
    intro d hdV hdR
    exact (ne_of_lt (Finset.mem_filter.mp hdV).2)
      (Finset.mem_filter.mp hdR).2.2
  have hcardUR : U.card = V.card + R.card := by
    rw [hU, Finset.card_union_of_disjoint hdisj]
  have hcardV : V.card = alphaRowPrefixCount T a i := rfl
  let W : Finset ℕ := U.image (fun d => d.val.val)
  have hWinj : Set.InjOn (fun d : AlphaRowCell T a => d.val.val) U := by
    intro d hd e he hde
    apply Subtype.ext
    apply Fin.ext
    exact hde
  have hW_eq : W = Finset.Ico (c.val.val + 1) (S.outer a) := by
    ext z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨d, hd, rfl⟩
      have hdU := (Finset.mem_filter.mp hd).2
      have hdrow := FiniteSkewShape.mem_rowCells.mp d.property
      exact Finset.mem_Ico.mpr ⟨Nat.succ_le_of_lt hdU, hdrow.2⟩
    · intro hz
      have hz' := Finset.mem_Ico.mp hz
      let d : AlphaRowCell T a := ⟨⟨z, by
        have houter := S.outer.rowLength_le_width a
        omega⟩, by
        apply FiniteSkewShape.mem_rowCells.mpr
        have hcrow := FiniteSkewShape.mem_rowCells.mp c.property
        have hinner : (S.inner a : ℕ) ≤ c.val.val := hcrow.1
        have hcz : c.val.val ≤ z := (Nat.le_succ _).trans hz'.1
        exact ⟨hinner.trans hcz, hz'.2⟩⟩
      have hdU : d ∈ U := by
        simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Nat.lt_of_succ_le hz'.1
      apply Finset.mem_image.mpr
      exact ⟨d, hdU, rfl⟩
  have hcardU : U.card = S.outer a - (c.val.val + 1) := by
    have hcardW : W.card = U.card := by
      dsimp [W]
      rw [Finset.card_image_iff.mpr hWinj]
    rw [← hcardW, hW_eq, Nat.card_Ico]
  have hmain : boundary.val + alphaRowPrefixCount T a i + R.card =
      boundary.val + (S.outer a - (c.val.val + 1)) := by
    calc
      boundary.val + alphaRowPrefixCount T a i + R.card =
          boundary.val + (V.card + R.card) := by
            simp [hcardV, Nat.add_assoc]
      _ = boundary.val + U.card := by rw [← hcardUR]
      _ = boundary.val + (S.outer a - (c.val.val + 1)) := by rw [hcardU]
  simpa [i, R] using hmain

/-! A local forward form of `alphaBlockPosition_move_spec`. -/
theorem alphaBlockPosition_move_of_source_add_rank
    {N : ℕ} (source : Fin (N + 1)) (d : ℕ)
    (hd : source.val + d ≤ N)
    (t : Fin (finiteFactorStageCount 1 0 N))
    (hsource : source.val ≤ t.val)
    (hrank : t.val - source.val < d) :
    (alphaBlockPosition source d hd t.castSucc).val = t.val ∧
      (alphaBlockPosition source d hd t.succ).val = t.val + 1 := by
  have ht : t.val < N := by simpa [finiteFactorStageCount] using t.isLt
  have hnextsource : source.val ≤ t.val + 1 := by omega
  have hmin : min d (t.val - source.val) = t.val - source.val :=
    Nat.min_eq_right (Nat.le_of_lt hrank)
  have hmin_next : min d (t.val + 1 - source.val) = t.val + 1 - source.val := by
    apply Nat.min_eq_right
    omega
  constructor <;>
    unfold alphaBlockPosition
  · simp only [Fin.val_castSucc, if_pos hsource]
    rw [hmin]
    omega
  · simp only [Fin.val_succ, if_pos hnextsource]
    rw [hmin_next]
    omega

theorem alphaRowBlockPosition_move_of_source_add_rank
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (boundary : Fin (N + 1)) (hbound : boundary.val + S.rowWidth a ≤ N)
    (i : Fin p) (k : Fin N)
    (hsource : (alphaRowBlockSource T a boundary hbound i).val ≤ k.val)
    (hrank : k.val - (alphaRowBlockSource T a boundary hbound i).val <
      alphaRowBlockCount T a i) :
    (alphaRowBlockPosition T a boundary hbound i k.castSucc).val = k.val ∧
      (alphaRowBlockPosition T a boundary hbound i k.succ).val = k.val + 1 := by
  let t : Fin (finiteFactorStageCount 1 0 N) :=
    ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
  have hmove := alphaBlockPosition_move_of_source_add_rank
    (alphaRowBlockSource T a boundary hbound i)
    (alphaRowBlockCount T a i)
    (alphaRowBlockSource_add_count_le T a boundary hbound i)
    t hsource hrank
  simpa [alphaRowBlockPosition, t] using hmove

theorem tupleAlphaTableauCell_source_add_tail_eq
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (c : AlphaRowCell T.tableaux.alphaTableau a) :
    (tupleNetworkSource J a).val +
        alphaRowPrefixCount T.tableaux.alphaTableau a (alphaRowBlock T.tableaux.alphaTableau a c) +
        (Finset.univ.filter fun d : AlphaRowCell T.tableaux.alphaTableau a =>
          c.val.val < d.val.val ∧
            alphaRowBlock T.tableaux.alphaTableau a d = alphaRowBlock T.tableaux.alphaTableau a c).card =
      J.tupleWidth - (a.rev.val + c.val.val + 1) := by
  have hbound := tupleCoproductTableau_alpha_row_bound_q_zero T a
  have htail := alphaRowBlockSource_add_tailCount_eq
    T.tableaux.alphaTableau a (tupleNetworkSource J a) hbound c
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  have houter : (T.intermediate.alphaShape.outer a : ℕ) = containingOuterPartition J a := by
    change T.intermediate.middle a = containingOuterPartition J a
    exact congrArg (fun M => M a) hmid
  have htail' :
      (tupleNetworkSource J a).val +
          alphaRowPrefixCount T.tableaux.alphaTableau a
            (alphaRowBlock T.tableaux.alphaTableau a c) +
          (Finset.univ.filter fun d : AlphaRowCell T.tableaux.alphaTableau a =>
            c.val.val < d.val.val ∧
              alphaRowBlock T.tableaux.alphaTableau a d =
                alphaRowBlock T.tableaux.alphaTableau a c).card =
        (tupleNetworkSource J a).val +
          (T.intermediate.alphaShape.outer a - (c.val.val + 1)) := by
    simpa using htail
  rw [houter] at htail'
  have hJ := J.value_le_tupleWidth a.rev
  have hpos := J.position_le a.rev
  have hcell := FiniteSkewShape.mem_rowCells.mp c.property
  have hcOuter : c.val.val < containingOuterPartition J a := by
    rw [← houter]
    exact hcell.2
  change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
  have hsub : a.rev.val + c.val.val + 1 ≤ J a.rev - 1 := by omega
  have hwidth : J a.rev - 1 ≤ J.tupleWidth := by omega
  have hsecond :
      J a.rev - (a.rev.val + 1) - (c.val.val + 1) =
        (J a.rev - 1) - (a.rev.val + c.val.val + 1) := by omega
  calc
    _ = (tupleNetworkSource J a).val +
        (J a.rev - (a.rev.val + 1) - (c.val.val + 1)) := by
          exact htail'
    _ = J.tupleWidth - (a.rev.val + c.val.val + 1) := by
      rw [tupleNetworkSource_val]
      rw [hsecond]
      exact Nat.sub_add_sub_cancel hwidth hsub

theorem alphaRowBlockTailCount_lt_blockCount
    {r N p : ℕ} {S : FiniteSkewShape r N}
    (T : AlphaSkewTableau S p) (a : Fin r)
    (c : AlphaRowCell T a) :
    (Finset.univ.filter fun d : AlphaRowCell T a =>
      c.val.val < d.val.val ∧
        alphaRowBlock T a d = alphaRowBlock T a c).card <
      alphaRowBlockCount T a (alphaRowBlock T a c) := by
  let B : Finset (AlphaRowCell T a) := Finset.univ.filter fun d =>
    alphaRowBlock T a d = alphaRowBlock T a c
  let R : Finset (AlphaRowCell T a) := Finset.univ.filter fun d =>
    c.val.val < d.val.val ∧ alphaRowBlock T a d = alphaRowBlock T a c
  have hsubset : R ⊆ B := by
    intro d hd
    change d ∈ Finset.univ.filter fun e =>
      alphaRowBlock T a e = alphaRowBlock T a c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hd).2.2
  have hcB : c ∈ B := by
    simp [B]
  have hcR : c ∉ R := by
    simp [R]
  have hne : R ≠ B := by
    intro heq
    have : c ∈ R := by rw [heq]; exact hcB
    exact hcR this
  have hssub : R ⊂ B := (Finset.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩
  have hcard := Finset.card_lt_card hssub
  simpa [R, B, alphaRowBlockCount] using hcard

theorem tupleAlphaTableauPath_cell_move
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (c : AlphaRowCell T.tableaux.alphaTableau a) :
    let i := alphaRowBlock T.tableaux.alphaTableau a c
    let k : Fin (tupleNetworkBound J) :=
      ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
        have hN : 0 < tupleNetworkBound J := by
          change 0 < J.tupleWidth
          have hJ := J.value_le_tupleWidth a.rev
          have hpos := J.position_le a.rev
          omega
        have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
        have houter : (T.intermediate.alphaShape.outer a : ℕ) =
            containingOuterPartition J a := by
          change T.intermediate.middle a = containingOuterPartition J a
          exact congrArg (fun M => M a) hmid
        have hc := FiniteSkewShape.mem_rowCells.mp c.property
        have hcOuter : c.val.val < containingOuterPartition J a := by
          rw [← houter]
          exact hc.2
        change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
        have hJ := J.value_le_tupleWidth a.rev
        have hpos := J.position_le a.rev
        exact Nat.sub_lt (by omega) (by omega)⟩
    ((tupleAlphaTableauPath D I J hstruct T hp a).position
        (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc).val = k.val ∧
      ((tupleAlphaTableauPath D I J hstruct T hp a).position
        (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ).val = k.val + 1 := by
  let A := T.tableaux.alphaTableau
  let boundary := tupleNetworkSource J a
  let hbound := tupleCoproductTableau_alpha_row_bound_q_zero T a
  let i : Fin p := alphaRowBlock A a c
  have hN : 0 < tupleNetworkBound J := by
    change 0 < J.tupleWidth
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  have houter : (T.intermediate.alphaShape.outer a : ℕ) =
      containingOuterPartition J a := by
    change T.intermediate.middle a = containingOuterPartition J a
    exact congrArg (fun M => M a) hmid
  have hc := FiniteSkewShape.mem_rowCells.mp c.property
  have hcOuter : c.val.val < containingOuterPartition J a := by
    rw [← houter]
    exact hc.2
  change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
  have hJ := J.value_le_tupleWidth a.rev
  have hpos := J.position_le a.rev
  let k : Fin (tupleNetworkBound J) :=
    ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
      exact Nat.sub_lt (by omega) (by omega)⟩
  let R : Finset (AlphaRowCell A a) := Finset.univ.filter fun d =>
    c.val.val < d.val.val ∧ alphaRowBlock A a d = i
  have hsum := tupleAlphaTableauCell_source_add_tail_eq D I J hstruct T hp a c
  have hsum' :
      (alphaRowBlockSource A a boundary hbound i).val + R.card = k.val := by
    unfold alphaRowBlockSource
    have htail := hsum
    simpa [A, boundary, hbound, i, R, k, alphaRowBlockSource] using htail
  have htail_lt : R.card < alphaRowBlockCount A a i := by
    simpa [R, i] using alphaRowBlockTailCount_lt_blockCount A a c
  have hsource : (alphaRowBlockSource A a boundary hbound i).val ≤ k.val := by
    omega
  have hrank : k.val - (alphaRowBlockSource A a boundary hbound i).val <
      alphaRowBlockCount A a i := by
    omega
  have hrowmove := alphaRowBlockPosition_move_of_source_add_rank A a boundary hbound i k
    hsource hrank
  have hstage_cur :
      (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc =
        (⟨i.val * tupleNetworkBound J + k.val, by
          simp only [finiteFactorStageCount]
          have hi := i.isLt
          have hk := k.isLt
          have hstep : i.val * tupleNetworkBound J + k.val <
              (i.val + 1) * tupleNetworkBound J := by
            calc
              i.val * tupleNetworkBound J + k.val <
                  i.val * tupleNetworkBound J + tupleNetworkBound J :=
                Nat.add_lt_add_left hk _
              _ = (i.val + 1) * tupleNetworkBound J := by simp [Nat.succ_mul]
          have hnext : (i.val + 1) * tupleNetworkBound J ≤
              p * tupleNetworkBound J := by
            simpa [Nat.mul_comm] using
              (Nat.mul_le_mul_right (tupleNetworkBound J)
                (Nat.succ_le_of_lt hi))
          omega⟩ : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) := by
    apply Fin.ext
    dsimp [alphaBlockStage]
    omega
  have hpos_cur :
      ((tupleAlphaTableauPath D I J hstruct T hp a).position
        (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc).val = k.val := by
    rw [tupleAlphaTableauPath_position, hstage_cur]
    rw [alphaTableauPosition_at_block_offset A a boundary hbound hN i k]
    exact hrowmove.1
  constructor
  · exact hpos_cur
  · by_cases hsame : k.val + 1 < tupleNetworkBound J
    · let kNext : Fin (tupleNetworkBound J) := ⟨k.val + 1, hsame⟩
      have hstage_next :
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ =
            (⟨i.val * tupleNetworkBound J + kNext.val, by
              simp only [finiteFactorStageCount]
              have hi := i.isLt
              have hk := kNext.isLt
              have hstep : i.val * tupleNetworkBound J + kNext.val <
                  (i.val + 1) * tupleNetworkBound J := by
                calc
                  i.val * tupleNetworkBound J + kNext.val <
                      i.val * tupleNetworkBound J + tupleNetworkBound J :=
                    Nat.add_lt_add_left hk _
                  _ = (i.val + 1) * tupleNetworkBound J := by simp [Nat.succ_mul]
              have hnext : (i.val + 1) * tupleNetworkBound J ≤
                  p * tupleNetworkBound J := by
                simpa [Nat.mul_comm] using
                  (Nat.mul_le_mul_right (tupleNetworkBound J)
                    (Nat.succ_le_of_lt hi))
              omega⟩ : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) := by
        apply Fin.ext
        dsimp [alphaBlockStage, kNext]
        omega
      have hnextpos :
          ((tupleAlphaTableauPath D I J hstruct T hp a).position
            (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ).val =
            k.val + 1 := by
        rw [tupleAlphaTableauPath_position, hstage_next]
        rw [alphaTableauPosition_at_block_offset A a boundary hbound hN i kNext]
        have hkNext :
            (⟨kNext.val, Nat.lt_succ_of_lt kNext.isLt⟩ :
              Fin (tupleNetworkBound J + 1)) = k.succ := by
          apply Fin.ext
          rfl
        rw [hkNext]
        exact hrowmove.2
      exact hnextpos
    · have hboundary : k.val + 1 = tupleNetworkBound J := by omega
      by_cases hfinal : i.val + 1 = p
      · have hstage_next :
            (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ =
              Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J)) := by
          apply Fin.ext
          simp only [alphaBlockStage, Fin.val_succ, Fin.last, Fin.val_mk,
            finiteFactorStageCount]
          calc
            0 + i.val * tupleNetworkBound J + k.val + 1 =
                i.val * tupleNetworkBound J + (k.val + 1) := by omega
            _ = i.val * tupleNetworkBound J + tupleNetworkBound J := by
              rw [hboundary]
            _ = (i.val + 1) * tupleNetworkBound J := by simp [Nat.succ_mul]
            _ = 0 + p * tupleNetworkBound J := by rw [hfinal]; simp
        have hkLast : k.succ = Fin.last (tupleNetworkBound J) := by
          apply Fin.ext
          exact hboundary
        have hrowEnd :
            (alphaRowBlockPosition A a boundary hbound i
              (Fin.last (tupleNetworkBound J))).val = k.val + 1 := by
          rw [← hkLast]
          exact hrowmove.2
        have hprefixlast := alphaRowPrefixCount_add_blockCount_last A a i hfinal
        have hsourceCount :
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i =
              boundary.val + T.intermediate.alphaShape.rowWidth a := by
          unfold alphaRowBlockSource
          change boundary.val + alphaRowPrefixCount A a i +
              alphaRowBlockCount A a i = boundary.val + T.intermediate.alphaShape.rowWidth a
          calc
            boundary.val + alphaRowPrefixCount A a i + alphaRowBlockCount A a i =
                boundary.val +
                  (alphaRowPrefixCount A a i + alphaRowBlockCount A a i) := by omega
            _ = boundary.val + T.intermediate.alphaShape.rowWidth a := by
              rw [hprefixlast]
        rw [tupleAlphaTableauPath_position, hstage_next]
        rw [alphaTableauPosition_last A a boundary hbound (by exact Nat.ne_of_gt hN)]
        rw [alphaRowBoundaryPosition_last]
        have hwidth : boundary.val + T.intermediate.alphaShape.rowWidth a = k.val + 1 := by
          calc
            boundary.val + T.intermediate.alphaShape.rowWidth a =
                (alphaRowBlockSource A a boundary hbound i).val +
                  alphaRowBlockCount A a i := hsourceCount.symm
            _ = (alphaRowBlockPosition A a boundary hbound i
                (Fin.last (tupleNetworkBound J))).val := by
              symm
              exact congrArg Fin.val
                (alphaRowBlockPosition_last A a boundary hbound i)
            _ = k.val + 1 := hrowEnd
        exact hwidth
      · have hiNext : i.val + 1 < p := by omega
        let iNext : Fin p := ⟨i.val + 1, hiNext⟩
        have hstage_next :
            (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ =
              (⟨iNext.val * tupleNetworkBound J, by
                simp only [finiteFactorStageCount]
                have hi := iNext.isLt
                have hmul := Nat.mul_lt_mul_of_pos_right iNext.isLt hN
                omega⟩ : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) := by
          apply Fin.ext
          dsimp [alphaBlockStage, iNext]
          calc
            0 + i.val * tupleNetworkBound J + k.val + 1 =
                i.val * tupleNetworkBound J + (k.val + 1) := by omega
            _ = i.val * tupleNetworkBound J + tupleNetworkBound J := by
              rw [hboundary]
            _ = (i.val + 1) * tupleNetworkBound J := by simp [Nat.succ_mul]
        have hkLast : k.succ = Fin.last (tupleNetworkBound J) := by
          apply Fin.ext
          exact hboundary
        have hrowEnd :
            (alphaRowBlockPosition A a boundary hbound i
              (Fin.last (tupleNetworkBound J))).val = k.val + 1 := by
          rw [← hkLast]
          exact hrowmove.2
        have hsourceCount :
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i = k.val + 1 := by
          calc
            (alphaRowBlockSource A a boundary hbound i).val +
                alphaRowBlockCount A a i =
              (alphaRowBlockPosition A a boundary hbound i
                (Fin.last (tupleNetworkBound J))).val := by
                  symm
                  exact congrArg Fin.val
                    (alphaRowBlockPosition_last A a boundary hbound i)
            _ = k.val + 1 := hrowEnd
        rw [tupleAlphaTableauPath_position, hstage_next]
        rw [alphaTableauPosition_at_block_boundary A a boundary hbound hN iNext]
        rw [alphaRowBlockSource_succ A a boundary hbound i hiNext]
        exact hsourceCount

theorem containingOuterPartition_diff_add_rev_gap
    {r : ℕ} (J : IncreasingIndexTuple r) {a b : Fin r} (hab : a < b) :
    (containingOuterPartition J a - containingOuterPartition J b) +
        (a.rev.val - b.rev.val) = J a.rev - J b.rev := by
  change (J a.rev - (a.rev.val + 1) -
      (J b.rev - (b.rev.val + 1))) +
        (a.rev.val - b.rev.val) = J a.rev - J b.rev
  let A₀ := J a.rev
  let B₀ := J b.rev
  let x₀ := a.rev.val + 1
  let y₀ := b.rev.val + 1
  have hA : x₀ ≤ A₀ := by simpa [A₀, x₀] using J.position_le a.rev
  have hB : y₀ ≤ B₀ := by simpa [B₀, y₀] using J.position_le b.rev
  have hxy : y₀ ≤ x₀ := by
    dsimp [x₀, y₀]
    have hrev := Fin.rev_lt_rev.mpr hab
    have hrevVal := Fin.mk_lt_mk.mp hrev
    omega
  have hsub : x₀ - y₀ ≤ A₀ - B₀ := by
    have hJlt : B₀ < A₀ := by
      dsimp [A₀, B₀]
      exact J.strictMono (Fin.rev_lt_rev.mpr hab)
    have hAB : B₀ ≤ A₀ := Nat.le_of_lt hJlt
    have hgap : a.rev.val - b.rev.val + J b.rev ≤ J a.rev :=
      strictMono_fin_gap J.strictMono (Fin.rev_lt_rev.mpr hab).le
    have hdiff : x₀ - y₀ = a.rev.val - b.rev.val := by
      dsimp [x₀, y₀]
      exact Nat.add_sub_add_right _ _ _
    apply (Nat.le_sub_iff_add_le hAB).2
    rw [hdiff]
    exact hgap
  have hrewrite : x₀ + (B₀ - y₀) = B₀ + (x₀ - y₀) := by
    calc
      x₀ + (B₀ - y₀) = x₀ + B₀ - y₀ :=
        (Nat.add_sub_assoc hB x₀).symm
      _ = B₀ + x₀ - y₀ := by rw [Nat.add_comm x₀ B₀]
      _ = B₀ + (x₀ - y₀) := Nat.add_sub_assoc hxy B₀
  have hmain : A₀ - x₀ - (B₀ - y₀) =
      (A₀ - B₀) - (x₀ - y₀) := by
    rw [Nat.sub_sub, hrewrite, ← Nat.sub_sub]
  have hcore :
      (A₀ - x₀ - (B₀ - y₀)) + (x₀ - y₀) = A₀ - B₀ := by
    calc
      (A₀ - x₀ - (B₀ - y₀)) + (x₀ - y₀) =
          ((A₀ - B₀) - (x₀ - y₀)) + (x₀ - y₀) := by rw [hmain]
      _ = A₀ - B₀ := Nat.sub_add_cancel hsub
  simpa [A₀, B₀, x₀, y₀] using hcore

theorem tupleAlphaTableauPath_block_separated
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) {a b : Fin r} (hab : a < b) (i : Fin p) :
    alphaRowBlockPosition T.tableaux.alphaTableau a
      (tupleNetworkSource J a)
      (tupleCoproductTableau_alpha_row_bound_q_zero T a) i (Fin.last (tupleNetworkBound J)) <
    alphaRowBlockPosition T.tableaux.alphaTableau b
      (tupleNetworkSource J b)
      (tupleCoproductTableau_alpha_row_bound_q_zero T b) i 0 := by
  let A := T.tableaux.alphaTableau
  have hcount := alphaRowPrefixCount_add_blockCount_le_of_row_lt A hab i
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  have hshape := hcount
  rw [show (T.intermediate.alphaShape.outer a : ℕ) = containingOuterPartition J a by
    change T.intermediate.middle a = containingOuterPartition J a
    exact congrArg (fun M => M a) hmid,
    show (T.intermediate.alphaShape.outer b : ℕ) = containingOuterPartition J b by
    change T.intermediate.middle b = containingOuterPartition J b
    exact congrArg (fun M => M b) hmid] at hshape
  change alphaRowPrefixCount A a i + alphaRowBlockCount A a i ≤
    alphaRowPrefixCount A b i +
      (J a.rev - (a.rev.val + 1) - (J b.rev - (b.rev.val + 1))) at hshape
  have hsource :
      (tupleNetworkSource J a).val + (J a.rev - J b.rev) =
        (tupleNetworkSource J b).val := by
    have hrev := Fin.rev_lt_rev.mpr hab
    have hJlt := J.strictMono hrev
    have hJposB := J.position_le b.rev
    have hsourceLe : (tupleNetworkSource J a).val ≤
        (tupleNetworkSource J b).val := by
      rw [tupleNetworkSource_val, tupleNetworkSource_val]
      omega
    have hdiff :
        (tupleNetworkSource J b).val - (tupleNetworkSource J a).val =
          J a.rev - J b.rev := by
      let A₀ := J a.rev - 1
      let B₀ := J b.rev - 1
      have hAB : A₀ - B₀ = J a.rev - J b.rev := by
        apply (Nat.sub_eq_iff_eq_add (by dsimp [A₀, B₀]; omega)).2
        have h := Nat.sub_add_sub_cancel (Nat.le_of_lt hJlt)
          (show 1 ≤ J b.rev by omega)
        dsimp [A₀, B₀]
        omega
      have hAwidth : A₀ ≤ J.tupleWidth := by
        dsimp [A₀]
        have hJwidthA := J.value_le_tupleWidth a.rev
        omega
      have hB_le_A : B₀ ≤ A₀ := by
        dsimp [A₀, B₀]
        omega
      have hdecomp :
          (tupleNetworkBound J - A₀) + (A₀ - B₀) =
            tupleNetworkBound J - B₀ := by
        exact Nat.sub_add_sub_cancel (by simpa [tupleNetworkBound] using hAwidth) hB_le_A
      change (J.tupleWidth - B₀) - (J.tupleWidth - A₀) = J a.rev - J b.rev
      rw [← hdecomp, Nat.add_sub_cancel_left, hAB]
    calc
      (tupleNetworkSource J a).val + (J a.rev - J b.rev) =
          (J a.rev - J b.rev) + (tupleNetworkSource J a).val := Nat.add_comm _ _
      _ = ((tupleNetworkSource J b).val - (tupleNetworkSource J a).val) +
          (tupleNetworkSource J a).val := by rw [hdiff]
      _ = (tupleNetworkSource J b).val := Nat.sub_add_cancel hsourceLe
  have houter := containingOuterPartition_diff_add_rev_gap J hab
  have houter' := houter
  change (J a.rev - (a.rev.val + 1) -
      (J b.rev - (b.rev.val + 1))) +
        (a.rev.val - b.rev.val) = J a.rev - J b.rev at houter'
  have hrev := Fin.rev_lt_rev.mpr hab
  have hgap : 1 ≤ a.rev.val - b.rev.val := by
    have hrevVal := Fin.mk_lt_mk.mp hrev
    omega
  have houterlt :
      J a.rev - (a.rev.val + 1) - (J b.rev - (b.rev.val + 1)) <
        J a.rev - J b.rev := by
    omega
  rw [alphaRowBlockPosition_last, alphaRowBlockPosition_zero]
  apply Fin.mk_lt_mk.mpr
  unfold alphaRowBlockSource
  change (tupleNetworkSource J a).val + alphaRowPrefixCount A a i +
      alphaRowBlockCount A a i <
    (tupleNetworkSource J b).val + alphaRowPrefixCount A b i
  rw [← hsource]
  have hle := Nat.add_le_add_left hshape (tupleNetworkSource J a).val
  omega

theorem tupleAlphaTableauPath_position_strict
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) {a b : Fin r} (hab : a < b)
    (s : Fin (finiteFactorStageCount p 0 (tupleNetworkBound J) + 1)) :
    (tupleAlphaTableauPath D I J hstruct T hp a).position s <
      (tupleAlphaTableauPath D I J hstruct T hp b).position s := by
  have hN : 0 < tupleNetworkBound J := by
    change 0 < J.tupleWidth
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hboundA := tupleCoproductTableau_alpha_row_bound_q_zero T a
  have hboundB := tupleCoproductTableau_alpha_row_bound_q_zero T b
  rw [tupleAlphaTableauPath_position, tupleAlphaTableauPath_position]
  by_cases hs : s.val < p * tupleNetworkBound J
  · let u : Fin (p * tupleNetworkBound J) := ⟨s.val, hs⟩
    let i : Fin p := alphaStageIndex u
    let k : Fin (tupleNetworkBound J + 1) :=
      ⟨s.val % tupleNetworkBound J, Nat.lt_succ_of_lt (Nat.mod_lt _ hN)⟩
    have hposA := alphaTableauPosition_of_internal T.tableaux.alphaTableau a
      (tupleNetworkSource J a) hboundA s hN.ne' hs
    have hposB := alphaTableauPosition_of_internal T.tableaux.alphaTableau b
      (tupleNetworkSource J b) hboundB s hN.ne' hs
    have hstage : i.val * tupleNetworkBound J + k.val = s.val := by
      simpa [i, k, u] using alphaStageIndex_mul_add_mod hN u
    have hstageA :
        alphaTableauPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
            hboundA s =
          alphaRowBlockPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
            hboundA i k := by
      simpa [i, k, u] using hposA
    have hstageB :
        alphaTableauPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
            hboundB s =
          alphaRowBlockPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
            hboundB i k := by
      simpa [i, k, u] using hposB
    rw [hstageA, hstageB]
    have hsep := tupleAlphaTableauPath_block_separated D I J hstruct T hp hab i
    have hleA := alphaBlockPosition_le_endpoint
      (alphaRowBlockSource T.tableaux.alphaTableau a (tupleNetworkSource J a)
        hboundA i)
      (alphaRowBlockCount T.tableaux.alphaTableau a i)
      (alphaRowBlockSource_add_count_le T.tableaux.alphaTableau a
        (tupleNetworkSource J a) hboundA i)
      ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
    have hgeB := alphaBlockPosition_ge_source
      (alphaRowBlockSource T.tableaux.alphaTableau b (tupleNetworkSource J b)
        hboundB i)
      (alphaRowBlockCount T.tableaux.alphaTableau b i)
      (alphaRowBlockSource_add_count_le T.tableaux.alphaTableau b
        (tupleNetworkSource J b) hboundB i)
      ⟨k.val, by simpa [finiteFactorStageCount] using k.isLt⟩
    apply Fin.mk_lt_mk.mpr
    have hsepVal := Fin.mk_lt_mk.mp hsep
    have hleA' :
        (alphaRowBlockPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
          hboundA i k).val ≤
          (alphaRowBlockPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
            hboundA i (Fin.last (tupleNetworkBound J))).val := by
      rw [alphaRowBlockPosition_last]
      exact hleA
    have hgeB' :
        (alphaRowBlockPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
          hboundB i 0).val ≤
          (alphaRowBlockPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
            hboundB i k).val := by
      rw [alphaRowBlockPosition_zero]
      exact hgeB
    exact lt_of_le_of_lt hleA' (lt_of_lt_of_le hsepVal hgeB')
  · have hlast : s = Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J)) := by
      apply Fin.ext
      simp only [Fin.last, Fin.val_mk, finiteFactorStageCount]
      have hslt := s.isLt
      simp only [finiteFactorStageCount] at hslt
      omega
    subst s
    have hfinalA :
        alphaTableauPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
            hboundA (Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J))) =
          tupleNetworkSink I J hstruct a := by
      rw [alphaTableauPosition_sink T.tableaux.alphaTableau a
        (tupleNetworkSource J a) hboundA hp]
      apply Fin.ext
      exact tupleCoproductTableau_alpha_row_endpoint_q_zero T a
    have hfinalB :
        alphaTableauPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
            hboundB (Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J))) =
          tupleNetworkSink I J hstruct b := by
      rw [alphaTableauPosition_sink T.tableaux.alphaTableau b
        (tupleNetworkSource J b) hboundB hp]
      apply Fin.ext
      exact tupleCoproductTableau_alpha_row_endpoint_q_zero T b
    calc
      alphaTableauPosition T.tableaux.alphaTableau a (tupleNetworkSource J a)
          hboundA (Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J))) =
          tupleNetworkSink I J hstruct a := hfinalA
      _ < tupleNetworkSink I J hstruct b := tupleNetworkSink_strictMono I J hstruct hab
      _ = alphaTableauPosition T.tableaux.alphaTableau b (tupleNetworkSource J b)
          hboundB (Fin.last (finiteFactorStageCount p 0 (tupleNetworkBound J))) := hfinalB.symm

noncomputable def tupleAlphaTableauTerm
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) : TupleFiniteFactorNetworkTerm D I J hstruct :=
  ⟨Equiv.refl (Fin r), fun a => tupleAlphaTableauPath D I J hstruct T hp a⟩

theorem tupleAlphaTableauTerm_good
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) :
    NetworkTermGood (tupleAlphaTableauTerm D I J hstruct T hp) := by
  intro a b hab s hcollision
  have hstrict := tupleAlphaTableauPath_position_strict D I J hstruct T hp hab s
  have hval := congrArg Fin.val hcollision
  exact (Nat.ne_of_lt (Fin.mk_lt_mk.mp hstrict)) hval

noncomputable def tupleAlphaTableauGoodFamily
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) : TupleVertexDisjointPathFamily D I J hstruct :=
  ⟨tupleAlphaTableauTerm D I J hstruct T hp,
    tupleAlphaTableauTerm_good D I J hstruct T hp⟩

theorem tupleAlphaTableauGoodFamily_intermediate
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) :
    (tupleAlphaTableauGoodFamily D I J hstruct T hp).intermediate = T.intermediate := by
  apply IntermediateRectanglePartition.middle_injective
  apply RectanglePartition.rowLength_injective
  funext a
  apply Fin.ext
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  have hboundary : betaBoundaryVertex p 0 J.tupleWidth = 0 := by
    apply Fin.ext
    simp [betaBoundaryVertex, finiteFactorStageCount]
  change reflectedWirePart a
      (((tupleAlphaTableauGoodFamily D I J hstruct T hp).1.2 a).position
        (betaBoundaryVertex p 0 J.tupleWidth)) = T.intermediate.middle a
  rw [hboundary]
  have hsource :
      ((tupleAlphaTableauGoodFamily D I J hstruct T hp).1.2 a).position 0 =
        tupleNetworkSource J a := by
    change (tupleAlphaTableauPath D I J hstruct T hp a).position 0 =
      tupleNetworkSource J a
    exact (tupleAlphaTableauPath D I J hstruct T hp a).source_eq
  rw [hsource, reflectedWirePart_source]
  exact (congrArg (fun M => M a) hmid).symm

theorem finiteSkewShape_cell_val_transport
    {r N : ℕ} {S U : FiniteSkewShape r N}
    (h : S = U) (x : S.Cell) : (h ▸ x).val = x.val := by
  cases h
  rfl

set_option maxHeartbeats 1000000 in
-- The dependent shape and crossing-stage transports in this reconstruction need a larger budget.
theorem tupleAlphaTableauGoodFamily_alphaCellCrossingStage
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (c : AlphaRowCell T.tableaux.alphaTableau a) :
    let F := tupleAlphaTableauGoodFamily D I J hstruct T hp
    let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
      congrArg (fun U => U.alphaShape)
        (tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp)
    let xT : T.intermediate.alphaShape.Cell :=
      ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
    let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
    alphaCellCrossingStage F xF =
      alphaBlockStage p 0 (tupleNetworkBound J)
        (alphaRowBlock T.tableaux.alphaTableau a c)
        ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
          have hN : 0 < tupleNetworkBound J := by
            change 0 < J.tupleWidth
            have hJ := J.value_le_tupleWidth a.rev
            have hpos := J.position_le a.rev
            omega
          have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
          have houter : (T.intermediate.alphaShape.outer a : ℕ) =
              containingOuterPartition J a := by
            change T.intermediate.middle a = containingOuterPartition J a
            exact congrArg (fun M => M a) hmid
          have hc := FiniteSkewShape.mem_rowCells.mp c.property
          have hcOuter : c.val.val < containingOuterPartition J a := by
            rw [← houter]
            exact hc.2
          change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
          exact Nat.sub_lt (by omega) (by omega)⟩ := by
  let F := tupleAlphaTableauGoodFamily D I J hstruct T hp
  let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
    congrArg (fun U => U.alphaShape)
      (tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp)
  let xT : T.intermediate.alphaShape.Cell :=
    ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
  let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
  let i : Fin p := alphaRowBlock T.tableaux.alphaTableau a c
  let k : Fin (tupleNetworkBound J) :=
    ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
      have hN : 0 < tupleNetworkBound J := by
        change 0 < J.tupleWidth
        have hJ := J.value_le_tupleWidth a.rev
        have hpos := J.position_le a.rev
        omega
      have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
      have houter : (T.intermediate.alphaShape.outer a : ℕ) =
          containingOuterPartition J a := by
        change T.intermediate.middle a = containingOuterPartition J a
        exact congrArg (fun M => M a) hmid
      have hc := FiniteSkewShape.mem_rowCells.mp c.property
      have hcOuter : c.val.val < containingOuterPartition J a := by
        rw [← houter]
        exact hc.2
      change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
      exact Nat.sub_lt (by omega) (by omega)⟩
  have hval : xF.val = xT.val := by
    simpa [xF] using finiteSkewShape_cell_val_transport hshape.symm xT
  have hrow : xF.val.1 = a := by
    have := congrArg Prod.fst hval
    simpa [xT] using this
  have hcol : xF.val.2.val = c.val.val := by
    have := congrArg (fun z : Fin r × Fin (tupleNetworkBound J) => z.2.val) hval
    simpa [xT] using this
  have hwire : (alphaCellCrossingWire F xF).val = k.val := by
    rw [alphaCellCrossingWire_val]
    rw [hrow, hcol]
  have hmove := tupleAlphaTableauPath_cell_move D I J hstruct T hp a c
  have hmove' :
      ((F.1.2 a).position (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc).val =
          k.val ∧
        ((F.1.2 a).position (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ).val =
          k.val + 1 := by
    simpa [F, tupleAlphaTableauGoodFamily, tupleAlphaTableauTerm, i, k] using hmove
  have hmoveF :
      ((F.1.2 xF.val.1).position
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc).val = k.val ∧
        ((F.1.2 xF.val.1).position
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ).val = k.val + 1 := by
    rw [hrow]
    exact hmove'
  have hbounds := alphaCell_crossing_bounds F xF
  have hsource_bound :
      (tupleNetworkSource J (F.1.1 a)).val ≤
        (alphaCellCrossingWire F xF).val := by
    simpa [hrow] using hbounds.1
  have hsink_bound :
      (alphaCellCrossingWire F xF).val <
        (tupleNetworkSink I J hstruct a).val := by
    simpa [hrow] using hbounds.2.1
  change alphaCellCrossingStage F xF = alphaBlockStage p 0
    (tupleNetworkBound J) i k
  unfold alphaCellCrossingStage
  symm
  apply (F.1.2 xF.val.1).crossingStage_unique
    (alphaCellCrossingWire F xF).val hbounds.1 hbounds.2.1
  constructor
  · calc
      ((F.1.2 xF.val.1).position
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).castSucc).val = k.val :=
        hmoveF.1
      _ = (alphaCellCrossingWire F xF).val := hwire.symm
  · calc
      ((F.1.2 xF.val.1).position
          (alphaBlockStage p 0 (tupleNetworkBound J) i k).succ).val = k.val + 1 := by
        exact hmoveF.2
      _ = (alphaCellCrossingWire F xF).val + 1 := by rw [hwire]

set_option maxHeartbeats 1000000 in
-- The dependent entry transport reuses the crossing-stage calculation and needs a larger budget.
theorem tupleAlphaTableauGoodFamily_alphaCellEntry_eq
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) (a : Fin r)
    (c : AlphaRowCell T.tableaux.alphaTableau a) :
    let F := tupleAlphaTableauGoodFamily D I J hstruct T hp
    let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
      congrArg (fun U => U.alphaShape)
        (tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp)
    let xT : T.intermediate.alphaShape.Cell :=
      ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
    let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
    alphaCellEntry F xF = T.tableaux.alphaTableau.entry xT := by
  let F := tupleAlphaTableauGoodFamily D I J hstruct T hp
  let hshape : F.intermediate.alphaShape = T.intermediate.alphaShape :=
    congrArg (fun U => U.alphaShape)
      (tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp)
  let xT : T.intermediate.alphaShape.Cell :=
    ⟨(a, c.val), by simpa [FiniteSkewShape.rowCells] using c.property⟩
  let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
  let i : Fin p := alphaRowBlock T.tableaux.alphaTableau a c
  let k : Fin (tupleNetworkBound J) :=
    ⟨tupleNetworkBound J - (a.rev.val + c.val.val + 1), by
      have hN : 0 < tupleNetworkBound J := by
        change 0 < J.tupleWidth
        have hJ := J.value_le_tupleWidth a.rev
        have hpos := J.position_le a.rev
        omega
      have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
      have houter : (T.intermediate.alphaShape.outer a : ℕ) =
          containingOuterPartition J a := by
        change T.intermediate.middle a = containingOuterPartition J a
        exact congrArg (fun M => M a) hmid
      have hc := FiniteSkewShape.mem_rowCells.mp c.property
      have hcOuter : c.val.val < containingOuterPartition J a := by
        rw [← houter]
        exact hc.2
      change c.val.val < J a.rev - (a.rev.val + 1) at hcOuter
      exact Nat.sub_lt (by omega) (by omega)⟩
  have hstage := tupleAlphaTableauGoodFamily_alphaCellCrossingStage D I J hstruct T hp a c
  have hstage' : alphaCellCrossingStage F xF = alphaBlockStage p 0
      (tupleNetworkBound J) i k := by
    simpa [F, hshape, xT, xF, i, k] using hstage
  change alphaCellEntry F xF = T.tableaux.alphaTableau.entry xT
  let eF : Fin p :=
    ⟨((alphaCellCrossingStage F xF).val - 0) /
        J.tupleWidth, alphaCellCrossingStage_alpha_index_bound F xF⟩
  have hN : 0 < tupleNetworkBound J := by
    change 0 < J.tupleWidth
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    omega
  have hstageVal := congrArg Fin.val hstage'
  have hdiv : eF.val = i.val := by
    dsimp [eF]
    rw [hstageVal]
    simp only [alphaBlockStage, tupleNetworkBound, Nat.zero_add]
    change (i.val * J.tupleWidth + k.val) / J.tupleWidth = i.val
    rw [Nat.mul_comm i.val J.tupleWidth, Nat.mul_add_div hN,
      Nat.div_eq_of_lt k.isLt]
    simp
  have hfin : eF = i := by
    apply Fin.ext
    exact hdiv
  change eF.rev = T.tableaux.alphaTableau.entry xT
  rw [hfin]
  simpa [i, alphaRowBlock, xT]

set_option maxHeartbeats 1000000 in
-- The final tableau equality combines dependent cell transports with total entry functions.
theorem canonicalGoodTableauMap_tupleAlphaTableauGoodFamily
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) :
    canonicalGoodTableauMap (tupleAlphaTableauGoodFamily D I J hstruct T hp) = T := by
  let F := tupleAlphaTableauGoodFamily D I J hstruct T hp
  let U := canonicalGoodTableauMap F
  have hmid : U.intermediate = T.intermediate := by
    change (tupleCoproductTableauOfPathFamily F).intermediate = T.intermediate
    simpa [F, U] using tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp
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
          (tupleAlphaTableauGoodFamily_intermediate D I J hstruct T hp)
      let xT : T.intermediate.alphaShape.Cell := ⟨(a, c), hT⟩
      let xF : F.intermediate.alphaShape.Cell := hshape.symm ▸ xT
      have hentry0 := tupleAlphaTableauGoodFamily_alphaCellEntry_eq
        D I J hstruct T hp a cRow
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
    exact Subsingleton.elim _ _

theorem canonicalGoodTableauMap_bijective_p_pos_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hp : 0 < p)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) :
    Function.Bijective (@canonicalGoodTableauMap p 0 r D I J hstruct) :=
  ⟨canonicalGoodTableauMap_injective_p_pos_q_zero D hp I J hstruct,
    fun T => ⟨tupleAlphaTableauGoodFamily D I J hstruct T hp,
      canonicalGoodTableauMap_tupleAlphaTableauGoodFamily D I J hstruct T hp⟩⟩

noncomputable def canonicalGoodBijectionBridge_p_pos_q_zero
    {p : ℕ} (D : FiniteEdreiData p 0) (hp : 0 < p) (hgamma : D.gamma = 0) :
    CanonicalGoodBijectionBridge D where
  gamma_eq_zero := hgamma
  bijective _ I J hstruct := canonicalGoodTableauMap_bijective_p_pos_q_zero
    D hp I J hstruct

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_p_pos_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hp : 0 < p) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := 0) I J hstruct,
        tupleCoproductWeight D I J hstruct T :=
  finiteFactorMinor_eq_tupleCoproductWeight_sum_of_canonicalBijection hgamma
    (canonicalGoodTableauMap_bijective_p_pos_q_zero D hp I J hstruct)

theorem finiteFactorMinor_pos_iff_indexHook_p_pos_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hp : 0 < p) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p 0 :=
  (canonicalGoodBijectionBridge_p_pos_q_zero D hp hgamma).finiteFactorMinor_pos_iff_indexHook I J

theorem finiteFactorMinor_eq_tupleCoproductWeight_sum_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :
    FiniteEdreiData.finiteFactorMinor D I J =
      ∑ T : TupleCoproductTableau (p := p) (q := 0) I J hstruct,
        tupleCoproductWeight D I J hstruct T := by
  cases p with
  | zero =>
      exact finiteFactorMinor_eq_tupleCoproductWeight_sum_p_zero D hgamma I J hstruct
  | succ p =>
      exact finiteFactorMinor_eq_tupleCoproductWeight_sum_p_pos_q_zero D
        (Nat.succ_pos p) hgamma I J hstruct

theorem finiteFactorMinor_pos_iff_indexHook_q_zero
    {p r : ℕ} (D : FiniteEdreiData p 0) (hgamma : D.gamma = 0)
    (I J : IncreasingIndexTuple r) :
    0 < FiniteEdreiData.finiteFactorMinor D I J ↔
      StructurallyAdmissible I J ∧ IndexHookInequalities I J p 0 := by
  cases p with
  | zero =>
      exact (canonicalGoodBijectionBridge_p_zero D hgamma).finiteFactorMinor_pos_iff_indexHook I J
  | succ p =>
      exact finiteFactorMinor_pos_iff_indexHook_p_pos_q_zero D
        (Nat.succ_pos p) hgamma I J

theorem tupleAlphaTableauPath_block_boundary_strict
    {p r : ℕ} (D : FiniteEdreiData p 0)
    (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J)
    (T : TupleCoproductTableau (p := p) (q := 0) I J hstruct)
    (hp : 0 < p) {a b : Fin r} (hab : a < b) (i : Fin p) :
    (alphaTableauPosition T.tableaux.alphaTableau a
      (tupleNetworkSource J a)
      (tupleCoproductTableau_alpha_row_bound_q_zero T a)
      ⟨i.val * tupleNetworkBound J, by
        simp only [finiteFactorStageCount]
        have hi := i.isLt
        have hJ := J.value_le_tupleWidth a.rev
        have hpos := J.position_le a.rev
        have hN : 0 < tupleNetworkBound J := by
          change 0 < J.tupleWidth
          omega
        have hiN : i.val * J.tupleWidth < p * J.tupleWidth :=
          Nat.mul_lt_mul_of_pos_right i.isLt hN
        simpa only [tupleNetworkBound, Nat.zero_add] using
          (Nat.lt_succ_of_lt hiN)
        ⟩) <
      (alphaTableauPosition T.tableaux.alphaTableau b
        (tupleNetworkSource J b)
        (tupleCoproductTableau_alpha_row_bound_q_zero T b)
        ⟨i.val * tupleNetworkBound J, by
          simp only [finiteFactorStageCount]
          have hi := i.isLt
          have hJ := J.value_le_tupleWidth b.rev
          have hpos := J.position_le b.rev
          have hN : 0 < tupleNetworkBound J := by
            change 0 < J.tupleWidth
            omega
          have hiN : i.val * J.tupleWidth < p * J.tupleWidth :=
            Nat.mul_lt_mul_of_pos_right i.isLt hN
          simpa only [tupleNetworkBound, Nat.zero_add] using
            (Nat.lt_succ_of_lt hiN)
          ⟩) := by
  have hN : 0 < tupleNetworkBound J := by
    have hJ := J.value_le_tupleWidth a.rev
    have hpos := J.position_le a.rev
    change 0 < J.tupleWidth
    omega
  let A := T.tableaux.alphaTableau
  have hcount := alphaRowPrefixCount_le_of_row_lt A hab i
  have hmid := tupleCoproductTableau_middle_eq_outer_q_zero T
  have houterA : (T.intermediate.alphaShape.outer a : ℕ) =
      (containingOuterPartition J a : ℕ) := by
    change T.intermediate.middle a = containingOuterPartition J a
    exact congrArg (fun M => M a) hmid
  have houterB : (T.intermediate.alphaShape.outer b : ℕ) =
      (containingOuterPartition J b : ℕ) := by
    change T.intermediate.middle b = containingOuterPartition J b
    exact congrArg (fun M => M b) hmid
  have hrev : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
  have hJlt := J.strictMono hrev
  have hJposA := J.position_le a.rev
  have hJposB := J.position_le b.rev
  have hsourceA := tupleNetworkSource J a
  have hsourceB := tupleNetworkSource J b
  have hboundA := tupleCoproductTableau_alpha_row_bound_q_zero T a
  have hboundB := tupleCoproductTableau_alpha_row_bound_q_zero T b
  have hposA := alphaTableauPosition_at_block_boundary A a (tupleNetworkSource J a)
    (by simpa only [tupleNetworkBound] using hboundA) hN i
  have hposB := alphaTableauPosition_at_block_boundary A b (tupleNetworkSource J b)
    (by simpa only [tupleNetworkBound] using hboundB) hN i
  rw [hposA, hposB]
  unfold alphaRowBlockSource at *
  change (tupleNetworkSource J a).val + alphaRowPrefixCount A a i <
    (tupleNetworkSource J b).val + alphaRowPrefixCount A b i
  have hshape := hcount
  rw [houterA, houterB] at hshape
  change alphaRowPrefixCount A a i ≤ alphaRowPrefixCount A b i +
    (containingOuterPartition J a - containingOuterPartition J b) at hshape
  change alphaRowPrefixCount A a i ≤ alphaRowPrefixCount A b i +
      (J a.rev - (a.rev.val + 1) -
        (J b.rev - (b.rev.val + 1))) at hshape
  simp only [containingOuterPartition, IncreasingIndexTuple.associatedRectanglePartition,
    IncreasingIndexTuple.associatedPart] at hshape
  have houterDiff :
      (J a.rev - (a.rev.val + 1) - (J b.rev - (b.rev.val + 1))) +
        (a.rev.val - b.rev.val) = J a.rev - J b.rev := by
    let A₀ := J a.rev
    let B₀ := J b.rev
    let x₀ := a.rev.val + 1
    let y₀ := b.rev.val + 1
    have hA : x₀ ≤ A₀ := by simpa [A₀, x₀] using J.position_le a.rev
    have hB : y₀ ≤ B₀ := by simpa [B₀, y₀] using J.position_le b.rev
    have hxy : y₀ ≤ x₀ := by
      dsimp [x₀, y₀]
      have := Fin.mk_lt_mk.mp hrev
      omega
    have hBy : y₀ ≤ B₀ := hB
    have hxySub : x₀ - y₀ ≤ A₀ - B₀ := by
      have hJlt := J.strictMono hrev
      have hJgap : a.rev.val - b.rev.val + J b.rev ≤ J a.rev :=
        strictMono_fin_gap J.strictMono hrev.le
      have hAB : B₀ ≤ A₀ := by
        dsimp [A₀, B₀]
        exact Nat.le_of_lt hJlt
      have hdiff : x₀ - y₀ = a.rev.val - b.rev.val := by
        dsimp [x₀, y₀]
        exact Nat.add_sub_add_right _ _ _
      apply (Nat.le_sub_iff_add_le hAB).2
      rw [hdiff]
      exact hJgap
    have hrewrite : x₀ + (B₀ - y₀) = B₀ + (x₀ - y₀) := by
      calc
        x₀ + (B₀ - y₀) = x₀ + B₀ - y₀ :=
          (Nat.add_sub_assoc hBy x₀).symm
        _ = B₀ + x₀ - y₀ := by rw [Nat.add_comm x₀ B₀]
        _ = B₀ + (x₀ - y₀) := Nat.add_sub_assoc hxy B₀
    have hmain : A₀ - x₀ - (B₀ - y₀) =
        (A₀ - B₀) - (x₀ - y₀) := by
      rw [Nat.sub_sub, hrewrite, ← Nat.sub_sub]
    have hcore :
        (A₀ - x₀ - (B₀ - y₀)) + (x₀ - y₀) = A₀ - B₀ := by
      calc
        (A₀ - x₀ - (B₀ - y₀)) + (x₀ - y₀) =
            ((A₀ - B₀) - (x₀ - y₀)) + (x₀ - y₀) := by rw [hmain]
        _ = A₀ - B₀ := Nat.sub_add_cancel hxySub
    simpa [A₀, B₀, x₀, y₀] using hcore
  have hstrict : alphaRowPrefixCount A a i <
      alphaRowPrefixCount A b i + (J a.rev - J b.rev) := by
    have hrevVal := Fin.mk_lt_mk.mp hrev
    have hgap : 1 ≤ a.rev.val - b.rev.val := by omega
    have hle := Nat.add_le_add_right hshape (a.rev.val - b.rev.val)
    have hle' :
        alphaRowPrefixCount A a i + (a.rev.val - b.rev.val) ≤
          alphaRowPrefixCount A b i + (J a.rev - J b.rev) := by
      calc
        alphaRowPrefixCount A a i + (a.rev.val - b.rev.val) ≤
            (alphaRowPrefixCount A b i +
              (J a.rev - (a.rev.val + 1) -
                (J b.rev - (b.rev.val + 1)))) +
              (a.rev.val - b.rev.val) := hle
        _ = alphaRowPrefixCount A b i + (J a.rev - J b.rev) := by
          rw [Nat.add_assoc, houterDiff]
    omega
  have hsourceDiff :
      (tupleNetworkSource J b).val - (tupleNetworkSource J a).val =
        J a.rev - J b.rev := by
    let A₀ := J a.rev - 1
    let B₀ := J b.rev - 1
    have hAB : A₀ - B₀ = J a.rev - J b.rev := by
      apply (Nat.sub_eq_iff_eq_add (by
        dsimp [A₀, B₀]
        omega)).2
      have h := Nat.sub_add_sub_cancel (Nat.le_of_lt hJlt)
        (show 1 ≤ J b.rev by omega)
      dsimp [A₀, B₀]
      omega
    have hAwidth : A₀ ≤ J.tupleWidth := by
      dsimp [A₀]
      have hJwidthA := J.value_le_tupleWidth a.rev
      omega
    have hB_le_A : B₀ ≤ A₀ := by
      dsimp [A₀, B₀]
      omega
    have hdecomp :
        (tupleNetworkBound J - A₀) + (A₀ - B₀) =
          tupleNetworkBound J - B₀ := by
      exact Nat.sub_add_sub_cancel (by simpa [tupleNetworkBound] using hAwidth)
        hB_le_A
    change (J.tupleWidth - B₀) - (J.tupleWidth - A₀) = J a.rev - J b.rev
    rw [← hdecomp, Nat.add_sub_cancel_left, hAB]
  have hsourceLe : (tupleNetworkSource J a).val ≤
      (tupleNetworkSource J b).val := by
    rw [tupleNetworkSource_val, tupleNetworkSource_val]
    have hJlt' := J.strictMono hrev
    omega
  have hsourceEq :
      (tupleNetworkSource J a).val + (J a.rev - J b.rev) =
        (tupleNetworkSource J b).val := by
    calc
      (tupleNetworkSource J a).val + (J a.rev - J b.rev) =
          (J a.rev - J b.rev) + (tupleNetworkSource J a).val := Nat.add_comm _ _
      _ = ((tupleNetworkSource J b).val - (tupleNetworkSource J a).val) +
          (tupleNetworkSource J a).val := by rw [hsourceDiff]
      _ = (tupleNetworkSource J b).val := Nat.sub_add_cancel hsourceLe
  rw [← hsourceEq]
  have h := Nat.add_lt_add_left hstrict (tupleNetworkSource J a).val
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

end

end ToeplitzPositroids.Edrei
