import ToeplitzPositroids.Edrei.FiniteFactorNetworkLGV
import Mathlib.Tactic

/-!
# Order preservation in good finite-factor network terms

In the layered finite-factor network, every edge either stays on its wire or moves up by one
wire.  Consequently, two vertex-disjoint paths ending at increasingly ordered sinks remain
strictly ordered at every earlier stage.  If the sources are also increasingly indexed, the
source permutation of a good determinant term must be the identity.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- Every allowed network step stays on its current wire or moves up exactly one wire. -/
theorem networkStepAllowed_same_or_succ {p q N t : ℕ} {x y : Fin (N + 1)}
    (hstep : NetworkStepAllowed p q N t x y) :
    y.val = x.val ∨ y.val = x.val + 1 := by
  unfold NetworkStepAllowed at hstep
  split at hstep
  · exact hstep
  · rcases hstep with hstep | hstep
    · exact Or.inl hstep
    · exact Or.inr hstep.2.2

/-- Successive vertices of a finite-factor path are equal or differ by one wire. -/
theorem FiniteFactorPath.position_step_same_or_succ
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount p q N)) :
    (P.position t.succ).val = (P.position t.castSucc).val ∨
      (P.position t.succ).val = (P.position t.castSucc).val + 1 :=
  networkStepAllowed_same_or_succ (P.valid t)

/-- A finite-factor path is weakly increasing in its stage parameter. -/
theorem FiniteFactorPath.position_monotone_of_network
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    Monotone P.position := by
  rw [Fin.monotone_iff_le_succ]
  intro t
  have hstep := P.position_step_same_or_succ t
  change (P.position t.castSucc).val ≤ (P.position t.succ).val
  omega

/-- In a good family with strictly ordered sinks, the paths are strictly ordered at every
stage. -/
theorem networkTermGood_position_lt
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)} (hsink : StrictMono sink)
    (T : FiniteFactorNetworkTerm D source sink) (hgood : NetworkTermGood T)
    {b c : Fin r} (hbc : b < c)
    (s : Fin (finiteFactorStageCount p q N + 1)) :
    (T.2 b).position s < (T.2 c).position s := by
  let L := finiteFactorStageCount p q N
  let P := T.2 b
  let Q := T.2 c
  have hlast :
      (P.position (Fin.last L)).val < (Q.position (Fin.last L)).val := by
    rw [P.sink_eq, Q.sink_eq]
    exact hsink hbc
  have hback : ∀ (n : ℕ) (hn : n ≤ L),
      (P.position ⟨n, Nat.lt_succ_of_le hn⟩).val <
        (Q.position ⟨n, Nat.lt_succ_of_le hn⟩).val := by
    intro n hn
    apply Nat.decreasingInduction (n := L) (motive := fun k hk ↦
      (P.position ⟨k, Nat.lt_succ_of_le hk⟩).val <
        (Q.position ⟨k, Nat.lt_succ_of_le hk⟩).val)
    · intro k hk ih
      let t : Fin L := ⟨k, hk⟩
      have hP := P.position_step_same_or_succ t
      have hQ := Q.position_step_same_or_succ t
      have hne : P.position t.castSucc ≠ Q.position t.castSucc :=
        hgood b c hbc t.castSucc
      have hneVal : (P.position t.castSucc).val ≠ (Q.position t.castSucc).val := by
        intro heq
        exact hne (Fin.ext heq)
      change (P.position t.castSucc).val < (Q.position t.castSucc).val
      change (P.position t.succ).val < (Q.position t.succ).val at ih
      omega
    · simpa [L] using hlast
    · exact hn
  simpa using hback s.val (Nat.le_of_lt_succ s.isLt)

/-- A vertex-disjoint determinant term with strictly ordered sources and sinks has the identity
source permutation. -/
theorem networkTermGood_perm_eq_refl
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (hsource : StrictMono source) (hsink : StrictMono sink)
    (T : FiniteFactorNetworkTerm D source sink) (hgood : NetworkTermGood T) :
    T.1 = Equiv.refl (Fin r) := by
  have hpermStrict : StrictMono T.1 := by
    intro b c hbc
    have hpos := networkTermGood_position_lt hsink T hgood hbc 0
    rw [(T.2 b).source_eq, (T.2 c).source_eq] at hpos
    exact hsource.lt_iff_lt.mp hpos
  apply Equiv.ext
  intro b
  let f : Fin r →o Fin r :=
    { toFun := T.1
      monotone' := hpermStrict.monotone }
  have hf : f = OrderHom.id := OrderHom.eq_id_of_injective f hpermStrict.injective
  exact DFunLike.congr_fun hf b

end

end ToeplitzPositroids.Edrei
