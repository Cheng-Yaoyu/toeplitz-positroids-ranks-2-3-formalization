import ToeplitzPositroids.Edrei.FiniteFactorNetworkConcrete
import ToeplitzPositroids.Edrei.FiniteFactorNetworkLGV

/-!
# First-collision cancellation for the finite-factor network

At the least collision stage, the prefixes of the least colliding pair are exchanged.  The
source permutation is composed with the corresponding transposition.  The operation preserves
the unsigned product of path weights and reverses the determinant sign.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

namespace FiniteFactorPath

/-- Replace the prefix of `P` through a collision vertex by the prefix of `Q`. -/
def swapPrefix {p q N : ℕ} {D : FiniteEdreiData p q}
    {sourceP sourceQ sinkP sinkQ : Fin (N + 1)}
    (P : FiniteFactorPath D N sourceP sinkP)
    (Q : FiniteFactorPath D N sourceQ sinkQ)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : P.position s = Q.position s) :
    FiniteFactorPath D N sourceQ sinkP where
  position u := if u ≤ s then Q.position u else P.position u
  source_eq := by simp [Q.source_eq]
  sink_eq := by
    by_cases hs : Fin.last (finiteFactorStageCount p q N) ≤ s
    · have hslast : s = Fin.last (finiteFactorStageCount p q N) := by
        apply Fin.ext
        apply le_antisymm (Nat.le_of_lt_succ s.isLt)
        change finiteFactorStageCount p q N ≤ s.val at hs
        exact hs
      simp only [if_pos hs]
      have hc := hcoll
      rw [hslast, P.sink_eq, Q.sink_eq] at hc
      rw [Q.sink_eq, ← hc]
    · simp [hs, P.sink_eq]
  valid := by
    intro t
    by_cases hbefore : t.succ ≤ s
    · have hcast : t.castSucc ≤ s := by
        change t.val ≤ s.val
        change t.val + 1 ≤ s.val at hbefore
        omega
      simp only [if_pos hcast, if_pos hbefore]
      exact Q.valid t
    · by_cases hafter : s < t.castSucc
      · have hcast : ¬t.castSucc ≤ s := not_le_of_gt hafter
        simp only [if_neg hcast, if_neg hbefore]
        exact P.valid t
      · have hboundary : t.castSucc = s := by
          apply Fin.ext
          change t.val = s.val
          change ¬(t.val + 1 ≤ s.val) at hbefore
          change ¬(s.val < t.val) at hafter
          omega
        simp only [if_pos (le_of_eq hboundary), if_neg hbefore]
        convert P.valid t using 1
        rw [hboundary, hcoll]

@[simp]
theorem swapPrefix_position_of_le {p q N : ℕ} {D : FiniteEdreiData p q}
    {sourceP sourceQ sinkP sinkQ : Fin (N + 1)}
    (P : FiniteFactorPath D N sourceP sinkP)
    (Q : FiniteFactorPath D N sourceQ sinkQ)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : P.position s = Q.position s)
    {u : Fin (finiteFactorStageCount p q N + 1)} (hu : u ≤ s) :
    (swapPrefix P Q s hcoll).position u = Q.position u := by
  simp [swapPrefix, hu]

@[simp]
theorem swapPrefix_position_of_lt {p q N : ℕ} {D : FiniteEdreiData p q}
    {sourceP sourceQ sinkP sinkQ : Fin (N + 1)}
    (P : FiniteFactorPath D N sourceP sinkP)
    (Q : FiniteFactorPath D N sourceQ sinkQ)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : P.position s = Q.position s)
    {u : Fin (finiteFactorStageCount p q N + 1)} (hu : s < u) :
    (swapPrefix P Q s hcoll).position u = P.position u := by
  simp [swapPrefix, not_le_of_gt hu]

theorem swapPrefix_pair_stepWeight {p q N : ℕ} {D : FiniteEdreiData p q}
    {sourceP sourceQ sinkP sinkQ : Fin (N + 1)}
    (P : FiniteFactorPath D N sourceP sinkP)
    (Q : FiniteFactorPath D N sourceQ sinkQ)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : P.position s = Q.position s)
    (t : Fin (finiteFactorStageCount p q N)) :
    FiniteEdreiData.networkStepWeight D N t.val
        ((swapPrefix P Q s hcoll).position t.castSucc)
        ((swapPrefix P Q s hcoll).position t.succ) *
      FiniteEdreiData.networkStepWeight D N t.val
        ((swapPrefix Q P s hcoll.symm).position t.castSucc)
        ((swapPrefix Q P s hcoll.symm).position t.succ) =
      FiniteEdreiData.networkStepWeight D N t.val
        (P.position t.castSucc) (P.position t.succ) *
      FiniteEdreiData.networkStepWeight D N t.val
        (Q.position t.castSucc) (Q.position t.succ) := by
  by_cases hbefore : t.succ ≤ s
  · have hcast : t.castSucc ≤ s := by
      change t.val ≤ s.val
      change t.val + 1 ≤ s.val at hbefore
      omega
    simp [swapPrefix_position_of_le P Q s hcoll hcast,
      swapPrefix_position_of_le P Q s hcoll hbefore,
      swapPrefix_position_of_le Q P s hcoll.symm hcast,
      swapPrefix_position_of_le Q P s hcoll.symm hbefore, mul_comm]
  · have hsucc : s < t.succ := lt_of_not_ge hbefore
    by_cases hboundary : t.castSucc ≤ s
    · have heq : t.castSucc = s := by
        apply Fin.ext
        change t.val = s.val
        change t.val ≤ s.val at hboundary
        change s.val < t.val + 1 at hsucc
        omega
      rw [swapPrefix_position_of_le P Q s hcoll hboundary,
        swapPrefix_position_of_lt P Q s hcoll hsucc,
        swapPrefix_position_of_le Q P s hcoll.symm hboundary,
        swapPrefix_position_of_lt Q P s hcoll.symm hsucc,
        heq, hcoll]
    · have hcast : s < t.castSucc := lt_of_not_ge hboundary
      rw [swapPrefix_position_of_lt P Q s hcoll hcast,
        swapPrefix_position_of_lt P Q s hcoll hsucc,
        swapPrefix_position_of_lt Q P s hcoll.symm hcast,
        swapPrefix_position_of_lt Q P s hcoll.symm hsucc]

/-- Swapping two prefixes preserves the product of their path weights. -/
theorem swapPrefix_weight_mul {p q N : ℕ} {D : FiniteEdreiData p q}
    {sourceP sourceQ sinkP sinkQ : Fin (N + 1)}
    (P : FiniteFactorPath D N sourceP sinkP)
    (Q : FiniteFactorPath D N sourceQ sinkQ)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : P.position s = Q.position s) :
    (swapPrefix P Q s hcoll).weight * (swapPrefix Q P s hcoll.symm).weight =
      P.weight * Q.weight := by
  unfold weight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro t _
  exact swapPrefix_pair_stepWeight P Q s hcoll t

end FiniteFactorPath

/-- Exchange the prefixes of paths `b` and `c` and transpose their source labels. -/
noncomputable def networkTermSwapAt
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (_hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    FiniteFactorNetworkTerm D source sink :=
  ⟨(Equiv.swap b c).trans T.1, by
    intro d
    by_cases hdb : d = b
    · subst d
      let P := FiniteFactorPath.swapPrefix (T.2 b) (T.2 c) s hcoll
      exact
        { position := P.position
          source_eq := by simpa using P.source_eq
          sink_eq := P.sink_eq
          valid := P.valid }
    · by_cases hdc : d = c
      · subst d
        let P := FiniteFactorPath.swapPrefix (T.2 c) (T.2 b) s hcoll.symm
        exact
          { position := P.position
            source_eq := by simpa using P.source_eq
            sink_eq := P.sink_eq
            valid := P.valid }
      · have hfix : Equiv.swap b c d = d :=
          Equiv.swap_apply_of_ne_of_ne hdb hdc
        exact
          { position := (T.2 d).position
            source_eq := by simpa [hfix] using (T.2 d).source_eq
            sink_eq := (T.2 d).sink_eq
            valid := (T.2 d).valid }⟩

@[simp]
theorem networkTermSwapAt_perm
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    (networkTermSwapAt T b c hbc s hcoll).1 = (Equiv.swap b c).trans T.1 :=
  rfl

@[simp]
theorem networkTermSwapAt_path_left_position
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    (u : Fin (finiteFactorStageCount p q N + 1)) :
    ((networkTermSwapAt T b c hbc s hcoll).2 b).position u =
      if u ≤ s then (T.2 c).position u else (T.2 b).position u := by
  simp [networkTermSwapAt, FiniteFactorPath.swapPrefix]

@[simp]
theorem networkTermSwapAt_path_right_position
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    (u : Fin (finiteFactorStageCount p q N + 1)) :
    ((networkTermSwapAt T b c hbc s hcoll).2 c).position u =
      if u ≤ s then (T.2 b).position u else (T.2 c).position u := by
  simp [networkTermSwapAt, FiniteFactorPath.swapPrefix, hbc.symm]

theorem networkTermSwapAt_path_of_ne_position
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c d : Fin r) (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    (u : Fin (finiteFactorStageCount p q N + 1)) :
    ((networkTermSwapAt T b c hbc s hcoll).2 d).position u = (T.2 d).position u := by
  simp [networkTermSwapAt, hdb, hdc]

/-- The selected pair still collides after its prefixes are exchanged. -/
theorem networkTermSwapAt_collides
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    NetworkPathsCollideAt (networkTermSwapAt T b c hbc s hcoll) b c s := by
  unfold NetworkPathsCollideAt at hcoll ⊢
  simp [networkTermSwapAt_path_left_position,
    networkTermSwapAt_path_right_position, hcoll]

/-- At the collision stage every path occupies the same vertex before and after the swap. -/
theorem networkTermSwapAt_position_at_collision
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c d : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    ((networkTermSwapAt T b c hbc s hcoll).2 d).position s = (T.2 d).position s := by
  by_cases hdb : d = b
  · subst d
    rw [networkTermSwapAt_path_left_position]
    rw [if_pos le_rfl]
    exact hcoll.symm
  · by_cases hdc : d = c
    · subst d
      rw [networkTermSwapAt_path_right_position]
      rw [if_pos le_rfl]
      exact hcoll
    · exact networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll s

/-- Isolate two distinguished factors in a finite product. -/
theorem fintype_prod_eq_mul_mul_prod_erase_two
    {r : ℕ} (f : Fin r → ℝ) (b c : Fin r) (hbc : b ≠ c) :
    ∏ d, f d = f b * f c * ∏ d ∈ (Finset.univ \ {b}) \ {c}, f d := by
  rw [show (∏ d, f d) = ∏ d ∈ Finset.univ, f d by rfl,
    Finset.prod_eq_mul_prod_diff_singleton_of_mem (i := b) (Finset.mem_univ b) f,
    Finset.prod_eq_mul_prod_diff_singleton_of_mem (i := c) (by simp [Ne.symm hbc]) f]
  ring

theorem networkTermSwapAt_path_left_weight
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    ((networkTermSwapAt T b c hbc s hcoll).2 b).weight =
      (FiniteFactorPath.swapPrefix (T.2 b) (T.2 c) s hcoll).weight := by
  unfold FiniteFactorPath.weight
  apply Finset.prod_congr rfl
  intro t _
  simp [networkTermSwapAt_path_left_position, FiniteFactorPath.swapPrefix]

theorem networkTermSwapAt_path_right_weight
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    ((networkTermSwapAt T b c hbc s hcoll).2 c).weight =
      (FiniteFactorPath.swapPrefix (T.2 c) (T.2 b) s hcoll.symm).weight := by
  unfold FiniteFactorPath.weight
  apply Finset.prod_congr rfl
  intro t _
  simp [networkTermSwapAt_path_right_position, FiniteFactorPath.swapPrefix]

theorem networkTermSwapAt_path_of_ne_weight
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c d : Fin r) (hbc : b ≠ c) (hdb : d ≠ b) (hdc : d ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    ((networkTermSwapAt T b c hbc s hcoll).2 d).weight = (T.2 d).weight := by
  unfold FiniteFactorPath.weight
  apply Finset.prod_congr rfl
  intro t _
  rw [networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll,
    networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll]

/-- Prefix exchange preserves the unsigned product over the entire path family. -/
theorem networkTermSwapAt_weight_product
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    (∏ d, ((networkTermSwapAt T b c hbc s hcoll).2 d).weight) =
      ∏ d, (T.2 d).weight := by
  rw [fintype_prod_eq_mul_mul_prod_erase_two _ b c hbc,
    fintype_prod_eq_mul_mul_prod_erase_two _ b c hbc,
    networkTermSwapAt_path_left_weight T b c hbc s hcoll,
    networkTermSwapAt_path_right_weight T b c hbc s hcoll,
    FiniteFactorPath.swapPrefix_weight_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro d hd
  have hdb : d ≠ b := by simpa using (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hd).1).2
  have hdc : d ≠ c := by simpa using (Finset.mem_sdiff.mp hd).2
  exact networkTermSwapAt_path_of_ne_weight T b c d hbc hdb hdc s hcoll

/-- The source transposition reverses the permutation sign. -/
theorem networkTermSwapAt_sign
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    (networkTermSwapAt T b c hbc s hcoll).1.sign = -T.1.sign := by
  rw [networkTermSwapAt_perm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap hbc]
  simp

/-- Consequently the signed determinant weight is negated. -/
theorem networkTermSwapAt_signedWeight
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    networkTermSignedWeight (networkTermSwapAt T b c hbc s hcoll) =
      -networkTermSignedWeight T := by
  unfold networkTermSignedWeight
  rw [networkTermSwapAt_sign T b c hbc s hcoll,
    networkTermSwapAt_weight_product T b c hbc s hcoll]
  push_cast
  ring

/-- Extensionality for network terms, stated in terms of path vertex functions. -/
theorem networkTerm_ext
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    {T U : FiniteFactorNetworkTerm D source sink}
    (hperm : T.1 = U.1)
    (hposition : ∀ d u, (T.2 d).position u = (U.2 d).position u) : T = U := by
  rcases T with ⟨σ, P⟩
  rcases U with ⟨τ, Q⟩
  dsimp at hperm
  subst τ
  congr 1
  funext d
  apply FiniteFactorPath.position_injective
  funext u
  exact hposition d u

/-- Repeating a prefix exchange at the same collision restores the original term. -/
theorem networkTermSwapAt_involutive
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    networkTermSwapAt (networkTermSwapAt T b c hbc s hcoll) b c hbc s
        (networkTermSwapAt_collides T b c hbc s hcoll) = T := by
  let U := networkTermSwapAt T b c hbc s hcoll
  let hcollU := networkTermSwapAt_collides T b c hbc s hcoll
  apply networkTerm_ext
  · ext d
    simp [Equiv.trans_apply]
  · intro d u
    by_cases hdb : d = b
    · subst d
      rw [networkTermSwapAt_path_left_position U b c hbc s hcollU]
      by_cases hu : u ≤ s
      · rw [if_pos hu, networkTermSwapAt_path_right_position T b c hbc s hcoll,
          if_pos hu]
      · rw [if_neg hu, networkTermSwapAt_path_left_position T b c hbc s hcoll,
          if_neg hu]
    · by_cases hdc : d = c
      · subst d
        rw [networkTermSwapAt_path_right_position U b c hbc s hcollU]
        by_cases hu : u ≤ s
        · rw [if_pos hu, networkTermSwapAt_path_left_position T b c hbc s hcoll,
            if_pos hu]
        · rw [if_neg hu, networkTermSwapAt_path_right_position T b c hbc s hcoll,
            if_neg hu]
      · rw [networkTermSwapAt_path_of_ne_position U b c d hbc hdb hdc s hcollU,
          networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll]

/-- Stages at which at least two paths of a term collide. -/
noncomputable def networkCollisionStageSet
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) :
    Finset (Fin (finiteFactorStageCount p q N + 1)) :=
  Finset.univ.filter fun s ↦ ∃ b c : Fin r, b < c ∧ NetworkPathsCollideAt T b c s

@[simp]
theorem mem_networkCollisionStageSet_iff
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    {T : FiniteFactorNetworkTerm D source sink}
    {s : Fin (finiteFactorStageCount p q N + 1)} :
    s ∈ networkCollisionStageSet T ↔
      ∃ b c : Fin r, b < c ∧ NetworkPathsCollideAt T b c s := by
  simp [networkCollisionStageSet]

theorem networkCollisionStageSet_nonempty
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    (networkCollisionStageSet T).Nonempty := by
  obtain ⟨z, hz⟩ := (networkCollisionSet_nonempty_iff_not_good T).2 hbad
  exact ⟨z.1, mem_networkCollisionStageSet_iff.2
    ⟨z.2.1, z.2.2, (mem_networkCollisionSet_iff.mp hz).1,
      (mem_networkCollisionSet_iff.mp hz).2⟩⟩

/-- The earliest collision stage of a bad term. -/
noncomputable def networkFirstCollisionStage
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    Fin (finiteFactorStageCount p q N + 1) :=
  (networkCollisionStageSet T).min' (networkCollisionStageSet_nonempty T hbad)

theorem networkFirstCollisionStage_mem
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    networkFirstCollisionStage T hbad ∈ networkCollisionStageSet T :=
  Finset.min'_mem _ _

theorem networkFirstCollisionStage_le
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T)
    {s : Fin (finiteFactorStageCount p q N + 1)} (hs : s ∈ networkCollisionStageSet T) :
    networkFirstCollisionStage T hbad ≤ s :=
  Finset.min'_le _ _ hs

/-- Ordered colliding path pairs at one fixed stage. -/
noncomputable local instance finPairLinearOrder (r : ℕ) : LinearOrder (Fin r × Fin r) :=
  LinearOrder.lift' (finProdFinEquiv : Fin r × Fin r ≃ Fin (r * r)) finProdFinEquiv.injective

noncomputable def networkCollisionPairSetAt
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (s : Fin (finiteFactorStageCount p q N + 1)) : Finset (Fin r × Fin r) :=
  Finset.univ.filter fun bc ↦ bc.1 < bc.2 ∧ NetworkPathsCollideAt T bc.1 bc.2 s

@[simp]
theorem mem_networkCollisionPairSetAt_iff
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    {T : FiniteFactorNetworkTerm D source sink}
    {s : Fin (finiteFactorStageCount p q N + 1)} {bc : Fin r × Fin r} :
    bc ∈ networkCollisionPairSetAt T s ↔
      bc.1 < bc.2 ∧ NetworkPathsCollideAt T bc.1 bc.2 s := by
  simp [networkCollisionPairSetAt]

theorem networkCollisionPairSetAt_nonempty
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    {s : Fin (finiteFactorStageCount p q N + 1)}
    (hs : s ∈ networkCollisionStageSet T) :
    (networkCollisionPairSetAt T s).Nonempty := by
  obtain ⟨b, c, hbc, hcoll⟩ := mem_networkCollisionStageSet_iff.mp hs
  exact ⟨(b, c), mem_networkCollisionPairSetAt_iff.2 ⟨hbc, hcoll⟩⟩

/-- The least colliding pair at the earliest collision stage. -/
noncomputable def networkFirstCollisionPair
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    Fin r × Fin r :=
  let s := networkFirstCollisionStage T hbad
  (networkCollisionPairSetAt T s).min'
    (networkCollisionPairSetAt_nonempty T (networkFirstCollisionStage_mem T hbad))

theorem networkFirstCollisionPair_mem
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    networkFirstCollisionPair T hbad ∈
      networkCollisionPairSetAt T (networkFirstCollisionStage T hbad) :=
  Finset.min'_mem _ _

theorem networkFirstCollisionPair_le
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T)
    {bc : Fin r × Fin r}
    (hbc : bc ∈ networkCollisionPairSetAt T (networkFirstCollisionStage T hbad)) :
    (finProdFinEquiv (networkFirstCollisionPair T hbad) : Fin (r * r)) ≤
      finProdFinEquiv bc := by
  exact Finset.min'_le _ _ hbc

/-- Up to and including the exchange stage, swapping prefixes simply transposes path labels. -/
theorem networkTermSwapAt_position_of_le
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c d : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    {u : Fin (finiteFactorStageCount p q N + 1)} (hu : u ≤ s) :
    ((networkTermSwapAt T b c hbc s hcoll).2 d).position u =
      (T.2 (Equiv.swap b c d)).position u := by
  by_cases hdb : d = b
  · subst d
    rw [networkTermSwapAt_path_left_position, if_pos hu, Equiv.swap_apply_left]
  · by_cases hdc : d = c
    · subst d
      rw [networkTermSwapAt_path_right_position, if_pos hu, Equiv.swap_apply_right]
    · rw [networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll]
      rw [Equiv.swap_apply_of_ne_of_ne hdb hdc]

theorem networkTermSwapAt_position_of_lt
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c d : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    {u : Fin (finiteFactorStageCount p q N + 1)} (hu : s < u) :
    ((networkTermSwapAt T b c hbc s hcoll).2 d).position u = (T.2 d).position u := by
  by_cases hdb : d = b
  · subst d
    rw [networkTermSwapAt_path_left_position, if_neg (not_le_of_gt hu)]
  · by_cases hdc : d = c
    · subst d
      rw [networkTermSwapAt_path_right_position, if_neg (not_le_of_gt hu)]
    · exact networkTermSwapAt_path_of_ne_position T b c d hbc hdb hdc s hcoll u

/-- A collision of the swapped family before the exchange stage yields an original collision at
the same stage. -/
theorem mem_networkCollisionStageSet_of_swap_le
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s)
    {u : Fin (finiteFactorStageCount p q N + 1)} (hu : u ≤ s)
    (huColl : u ∈ networkCollisionStageSet (networkTermSwapAt T b c hbc s hcoll)) :
    u ∈ networkCollisionStageSet T := by
  obtain ⟨d, e, hde, hcollision⟩ := mem_networkCollisionStageSet_iff.mp huColl
  let d' := Equiv.swap b c d
  let e' := Equiv.swap b c e
  have hne : d' ≠ e' := by
    intro h
    exact (ne_of_lt hde) ((Equiv.swap b c).injective h)
  have hcollision' : NetworkPathsCollideAt T d' e' u := by
    unfold NetworkPathsCollideAt at hcollision ⊢
    simpa [d', e', networkTermSwapAt_position_of_le T b c d hbc s hcoll hu,
      networkTermSwapAt_position_of_le T b c e hbc s hcoll hu] using hcollision
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact mem_networkCollisionStageSet_iff.2 ⟨d', e', hlt, hcollision'⟩
  · exact mem_networkCollisionStageSet_iff.2 ⟨e', d', hgt, hcollision'.symm⟩

/-- Prefix exchange at the selected collision does not change the earliest collision stage. -/
theorem networkFirstCollisionStage_swap
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    let s := networkFirstCollisionStage T hbad
    let bc := networkFirstCollisionPair T hbad
    let hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
    let U := networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2
    let hbadU : ¬NetworkTermGood U := by
      intro hgood
      exact hgood bc.1 bc.2 hmem.1 s
        (networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2)
    networkFirstCollisionStage U hbadU = s := by
  dsimp only
  let s := networkFirstCollisionStage T hbad
  let bc := networkFirstCollisionPair T hbad
  have hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  let U := networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2
  have hcollU : NetworkPathsCollideAt U bc.1 bc.2 s :=
    networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2
  have hbadU : ¬NetworkTermGood U := by
    intro hgood
    exact hgood bc.1 bc.2 hmem.1 s hcollU
  apply le_antisymm
  · apply networkFirstCollisionStage_le U hbadU
    exact mem_networkCollisionStageSet_iff.2 ⟨bc.1, bc.2, hmem.1, hcollU⟩
  · let u := networkFirstCollisionStage U hbadU
    have huMem : u ∈ networkCollisionStageSet U := networkFirstCollisionStage_mem U hbadU
    by_contra hnot
    have hus : u ≤ s := le_of_lt (lt_of_not_ge hnot)
    have huOriginal : u ∈ networkCollisionStageSet T :=
      mem_networkCollisionStageSet_of_swap_le T bc.1 bc.2 hmem.1.ne s hmem.2 hus huMem
    have hsu := networkFirstCollisionStage_le T hbad huOriginal
    exact (not_lt_of_ge hsu) (lt_of_not_ge hnot)

/-- The set of colliding pairs at the exchange stage is unchanged. -/
theorem networkCollisionPairSetAt_swap
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (hbc : b ≠ c)
    (s : Fin (finiteFactorStageCount p q N + 1))
    (hcoll : NetworkPathsCollideAt T b c s) :
    networkCollisionPairSetAt (networkTermSwapAt T b c hbc s hcoll) s =
      networkCollisionPairSetAt T s := by
  ext de
  simp only [mem_networkCollisionPairSetAt_iff]
  constructor
  · rintro ⟨hde, hcollision⟩
    refine ⟨hde, ?_⟩
    unfold NetworkPathsCollideAt at hcollision ⊢
    simpa only [networkTermSwapAt_position_at_collision] using hcollision
  · rintro ⟨hde, hcollision⟩
    refine ⟨hde, ?_⟩
    unfold NetworkPathsCollideAt at hcollision ⊢
    simpa only [networkTermSwapAt_position_at_collision] using hcollision

/-- Prefix exchange at the selected collision also preserves the least pair at that stage. -/
theorem networkFirstCollisionPair_swap
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    let s := networkFirstCollisionStage T hbad
    let bc := networkFirstCollisionPair T hbad
    let hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
    let U := networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2
    let hbadU : ¬NetworkTermGood U := by
      intro hgood
      exact hgood bc.1 bc.2 hmem.1 s
        (networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2)
    networkFirstCollisionPair U hbadU = bc := by
  dsimp only
  let s := networkFirstCollisionStage T hbad
  let bc := networkFirstCollisionPair T hbad
  have hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  let U := networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2
  have hcollU : NetworkPathsCollideAt U bc.1 bc.2 s :=
    networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2
  have hbadU : ¬NetworkTermGood U := by
    intro hgood
    exact hgood bc.1 bc.2 hmem.1 s hcollU
  have hstage : networkFirstCollisionStage U hbadU = s := by
    simpa [s, bc, U] using networkFirstCollisionStage_swap T hbad
  change networkFirstCollisionPair U hbadU = bc
  apply finProdFinEquiv.injective
  apply le_antisymm
  · apply networkFirstCollisionPair_le U hbadU
    rw [hstage, networkCollisionPairSetAt_swap T bc.1 bc.2 hmem.1.ne s hmem.2]
    exact networkFirstCollisionPair_mem T hbad
  · apply networkFirstCollisionPair_le T hbad
    have hpairMem := networkFirstCollisionPair_mem U hbadU
    rw [hstage, networkCollisionPairSetAt_swap T bc.1 bc.2 hmem.1.ne s hmem.2] at hpairMem
    exact hpairMem

/-- The canonical first-collision prefix exchange on a bad term. -/
noncomputable def networkCanonicalSwap
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    FiniteFactorNetworkTerm D source sink :=
  let s := networkFirstCollisionStage T hbad
  let bc := networkFirstCollisionPair T hbad
  let hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2

theorem networkCanonicalSwap_not_good
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    ¬NetworkTermGood (networkCanonicalSwap T hbad) := by
  let s := networkFirstCollisionStage T hbad
  let bc := networkFirstCollisionPair T hbad
  have hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  intro hgood
  exact hgood bc.1 bc.2 hmem.1 s <| by
    simpa [networkCanonicalSwap, s, bc] using
      networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2

theorem networkCanonicalSwap_signedWeight
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    networkTermSignedWeight (networkCanonicalSwap T hbad) =
      -networkTermSignedWeight T := by
  unfold networkCanonicalSwap
  exact networkTermSwapAt_signedWeight _ _ _ _ _ _

@[simp]
theorem networkCanonicalSwap_perm
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    (networkCanonicalSwap T hbad).1 =
      (Equiv.swap (networkFirstCollisionPair T hbad).1
        (networkFirstCollisionPair T hbad).2).trans T.1 :=
  rfl

theorem networkCanonicalSwap_position_of_le
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T)
    (d : Fin r) {u : Fin (finiteFactorStageCount p q N + 1)}
    (hu : u ≤ networkFirstCollisionStage T hbad) :
    ((networkCanonicalSwap T hbad).2 d).position u =
      (T.2 (Equiv.swap (networkFirstCollisionPair T hbad).1
        (networkFirstCollisionPair T hbad).2 d)).position u := by
  unfold networkCanonicalSwap
  dsimp only
  exact networkTermSwapAt_position_of_le T _ _ d _ _ _ hu

theorem networkCanonicalSwap_position_of_lt
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T)
    (d : Fin r) {u : Fin (finiteFactorStageCount p q N + 1)}
    (hu : networkFirstCollisionStage T hbad < u) :
    ((networkCanonicalSwap T hbad).2 d).position u = (T.2 d).position u := by
  unfold networkCanonicalSwap
  dsimp only
  let bc := networkFirstCollisionPair T hbad
  have hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  by_cases hdb : d = bc.1
  · subst d
    rw [networkTermSwapAt_path_left_position, if_neg (not_le_of_gt hu)]
  · by_cases hdc : d = bc.2
    · subst d
      rw [networkTermSwapAt_path_right_position, if_neg (not_le_of_gt hu)]
    · exact networkTermSwapAt_path_of_ne_position _ _ _ _ hmem.1.ne hdb hdc _ _ _

theorem networkCanonicalSwap_involutive
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (hbad : ¬NetworkTermGood T) :
    networkCanonicalSwap (networkCanonicalSwap T hbad)
        (networkCanonicalSwap_not_good T hbad) = T := by
  let s := networkFirstCollisionStage T hbad
  let bc := networkFirstCollisionPair T hbad
  have hmem := mem_networkCollisionPairSetAt_iff.mp (networkFirstCollisionPair_mem T hbad)
  let U := networkTermSwapAt T bc.1 bc.2 hmem.1.ne s hmem.2
  have hbadU : ¬NetworkTermGood U := by
    intro hgood
    exact hgood bc.1 bc.2 hmem.1 s <| by
      simpa [U] using networkTermSwapAt_collides T bc.1 bc.2 hmem.1.ne s hmem.2
  have hstage : networkFirstCollisionStage U hbadU = s := by
    simpa [s, bc, U] using networkFirstCollisionStage_swap T hbad
  have hpair : networkFirstCollisionPair U hbadU = bc := by
    simpa [s, bc, U] using networkFirstCollisionPair_swap T hbad
  change networkCanonicalSwap U hbadU = T
  apply networkTerm_ext
  · ext d
    simp only [networkCanonicalSwap_perm, Equiv.trans_apply]
    rw [hpair]
    have hUperm : U.1 = (Equiv.swap bc.1 bc.2).trans T.1 := rfl
    rw [hUperm]
    simp only [Equiv.trans_apply]
    exact congrArg Fin.val (congrArg T.1 (Equiv.swap_apply_self bc.1 bc.2 d))
  · intro d u
    by_cases hu : u ≤ s
    · have huU : u ≤ networkFirstCollisionStage U hbadU := by simpa [hstage]
      rw [networkCanonicalSwap_position_of_le U hbadU d huU, hpair,
        networkTermSwapAt_position_of_le T bc.1 bc.2 _ hmem.1.ne s hmem.2 hu]
      rw [Equiv.swap_apply_self]
    · have hsu : s < u := lt_of_not_ge hu
      have hsuU : networkFirstCollisionStage U hbadU < u := by simpa [hstage]
      rw [networkCanonicalSwap_position_of_lt U hbadU d hsuU,
        networkTermSwapAt_position_of_lt T bc.1 bc.2 d hmem.1.ne s hmem.2 hsu]

/-- The canonical swap as an equivalence of the bad network terms. -/
noncomputable def networkBadTermSwapEquiv
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)} :
    {T : FiniteFactorNetworkTerm D source sink // ¬NetworkTermGood T} ≃
      {T : FiniteFactorNetworkTerm D source sink // ¬NetworkTermGood T} where
  toFun T := ⟨networkCanonicalSwap T.1 T.2, networkCanonicalSwap_not_good T.1 T.2⟩
  invFun T := ⟨networkCanonicalSwap T.1 T.2, networkCanonicalSwap_not_good T.1 T.2⟩
  left_inv T := by
    apply Subtype.ext
    exact networkCanonicalSwap_involutive T.1 T.2
  right_inv T := by
    apply Subtype.ext
    exact networkCanonicalSwap_involutive T.1 T.2

/-- The least-collision construction supplies the cancellation datum required by LGV. -/
noncomputable def finiteFactorNetworkCancellation
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)} :
    SignReversingInvolution (FiniteFactorNetworkTerm D source sink)
      (fun T ↦ ¬NetworkTermGood T) networkTermSignedWeight where
  swap := networkBadTermSwapEquiv
  involutive T := by
    apply Subtype.ext
    exact networkCanonicalSwap_involutive T.1 T.2
  weight_neg T := networkCanonicalSwap_signedWeight T.1 T.2

/-- The determinant of the path-sum matrix is its Leibniz sum over network terms. -/
theorem det_pathSumMatrix_eq_sum_networkTerms
    {p q r N : ℕ} (D : FiniteEdreiData p q)
    (source sink : Fin r → Fin (N + 1)) :
    Matrix.det ((fun a b ↦ FiniteFactorPath.pathSum D N (source a) (sink b)) :
      Matrix (Fin r) (Fin r) ℝ) =
      ∑ T : FiniteFactorNetworkTerm D source sink, networkTermSignedWeight T := by
  rw [Matrix.det_apply']
  simp only [FiniteFactorPath.pathSum, networkTermSignedWeight]
  simp_rw [Finset.prod_univ_sum]
  simp only [Fintype.piFinset_univ]
  simp_rw [Finset.mul_sum]
  exact (Fintype.sum_sigma (fun T : FiniteFactorNetworkTerm D source sink ↦
    (T.1.sign : ℤ) * ∏ b, (T.2 b).weight)).symm

/-- The complete finite network gives an unconditional LGV expansion of its path-sum minor. -/
noncomputable def finiteFactorNetworkLGVExpansion
    {p q r N : ℕ} (D : FiniteEdreiData p q)
    (source sink : Fin r → Fin (N + 1)) :
    LGVExpansion (Matrix.det ((fun a b ↦ FiniteFactorPath.pathSum D N (source a) (sink b)) :
      Matrix (Fin r) (Fin r) ℝ)) where
  term := FiniteFactorNetworkTerm D source sink
  termFintype := inferInstance
  good := NetworkTermGood
  goodDecidable := inferInstance
  signedWeight := networkTermSignedWeight
  value_eq_sum := det_pathSumMatrix_eq_sum_networkTerms D source sink
  cancellation := finiteFactorNetworkCancellation

end ToeplitzPositroids.Edrei
