import ToeplitzPositroids.Edrei.FiniteFactorNetworkLGV
import ToeplitzPositroids.Edrei.SkewTableauFromTuple
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic

/-!
# Vertex-disjoint finite-factor paths and supersymmetric tableaux

The elementary finite-factor network visits both finite alphabets from left to right.  Under the
reflected endpoint convention used below, a path deletes the rightmost cell of a partition whenever
it moves up one wire.  Consequently the network has to use the reversed alpha and beta alphabets in
order for increasing network time to give the usual increasing tableau entries.  Reversing either
finite alphabet does not change its commutative product, so it does not change the finite Edrei
series.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

noncomputable section

/-- Reverse both finite alphabets without changing the exponential parameter. -/
def reverseFiniteEdreiData {p q : ℕ} (D : FiniteEdreiData p q) : FiniteEdreiData p q where
  alpha i := D.alpha i.rev
  beta j := D.beta j.rev
  gamma := D.gamma
  alpha_pos i := D.alpha_pos i.rev
  beta_pos j := D.beta_pos j.rev
  gamma_nonneg := D.gamma_nonneg

@[simp]
theorem reverseFiniteEdreiData_alpha {p q : ℕ} (D : FiniteEdreiData p q) (i : Fin p) :
    (reverseFiniteEdreiData D).alpha i = D.alpha i.rev :=
  rfl

@[simp]
theorem reverseFiniteEdreiData_beta {p q : ℕ} (D : FiniteEdreiData p q) (j : Fin q) :
    (reverseFiniteEdreiData D).beta j = D.beta j.rev :=
  rfl

@[simp]
theorem reverseFiniteEdreiData_gamma {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).gamma = D.gamma :=
  rfl

@[simp]
theorem reverseFiniteEdreiData_betaProduct {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).betaProduct = D.betaProduct := by
  unfold FiniteEdreiData.betaProduct
  exact Fin.rev_bijective.prod_comp
    (fun j : Fin q ↦ FiniteEdreiData.betaFactor (D.beta j))

@[simp]
theorem reverseFiniteEdreiData_alphaProduct {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).alphaProduct = D.alphaProduct := by
  unfold FiniteEdreiData.alphaProduct
  exact Fin.rev_bijective.prod_comp
    (fun i : Fin p ↦ FiniteEdreiData.alphaFactor (D.alpha i))

@[simp]
theorem reverseFiniteEdreiData_exponentialFactor {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).exponentialFactor = D.exponentialFactor :=
  rfl

@[simp]
theorem reverseFiniteEdreiData_series {p q : ℕ} (D : FiniteEdreiData p q) :
    (reverseFiniteEdreiData D).series = D.series := by
  simp [FiniteEdreiData.series]

@[simp]
theorem reverseFiniteEdreiData_natCoefficient {p q : ℕ} (D : FiniteEdreiData p q) (n : ℕ) :
    (reverseFiniteEdreiData D).natCoefficient n = D.natCoefficient n := by
  simp [FiniteEdreiData.natCoefficient]

/-- The reflected wire bound used for a tuple minor. -/
abbrev tupleNetworkBound {r : ℕ} (J : IncreasingIndexTuple r) : ℕ :=
  J.tupleWidth

/-- Reflected outer endpoints, indexed in partition-row order rather than tuple order. -/
def tupleNetworkSource {r : ℕ} (J : IncreasingIndexTuple r) (a : Fin r) :
    Fin (tupleNetworkBound J + 1) :=
  ⟨J.tupleWidth - (J a.rev - 1), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

/-- Reflected inner endpoints. -/
def tupleNetworkSink {r : ℕ} (I J : IncreasingIndexTuple r)
    (_hstruct : StructurallyAdmissible I J) (a : Fin r) :
    Fin (tupleNetworkBound J + 1) :=
  ⟨J.tupleWidth - (I a.rev - 1), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

@[simp]
theorem tupleNetworkSource_val {r : ℕ} (J : IncreasingIndexTuple r) (a : Fin r) :
    (tupleNetworkSource J a).val = J.tupleWidth - (J a.rev - 1) :=
  rfl

@[simp]
theorem tupleNetworkSink_val {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) (a : Fin r) :
    (tupleNetworkSink I J hstruct a).val = J.tupleWidth - (I a.rev - 1) :=
  rfl

theorem tupleNetworkSource_le_sink {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) (a : Fin r) :
    tupleNetworkSource J a ≤ tupleNetworkSink I J hstruct a := by
  change J.tupleWidth - (J a.rev - 1) ≤ J.tupleWidth - (I a.rev - 1)
  exact Nat.sub_le_sub_left (Nat.sub_le_sub_right (hstruct a.rev) 1) _

/-- The path displacement is the corresponding componentwise tuple difference. -/
theorem tupleNetwork_displacement {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) (a : Fin r) :
    (tupleNetworkSink I J hstruct a).val - (tupleNetworkSource J a).val =
      J a.rev - I a.rev := by
  have hIJ := hstruct a.rev
  have hJ := J.value_le_tupleWidth a.rev
  have hIpos := I.position_le a.rev
  have hJpos := J.position_le a.rev
  simp only [tupleNetworkSink_val, tupleNetworkSource_val]
  omega

theorem tupleNetworkSource_strictMono {r : ℕ} (J : IncreasingIndexTuple r) :
    StrictMono (tupleNetworkSource J) := by
  intro a b hab
  have hrev : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
  have hJlt := J.strictMono hrev
  have haJ := J.value_le_tupleWidth a.rev
  have hbJ := J.value_le_tupleWidth b.rev
  have haPos := J.position_le a.rev
  have hbPos := J.position_le b.rev
  change J.tupleWidth - (J a.rev - 1) < J.tupleWidth - (J b.rev - 1)
  omega

theorem tupleNetworkSink_strictMono {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) :
    StrictMono (tupleNetworkSink I J hstruct) := by
  intro a b hab
  have hrev : b.rev < a.rev := Fin.rev_lt_rev.mpr hab
  have hIlt := I.strictMono hrev
  have haI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  have hbI := (hstruct b.rev).trans (J.value_le_tupleWidth b.rev)
  have haPos := I.position_le a.rev
  have hbPos := I.position_le b.rev
  change J.tupleWidth - (I a.rev - 1) < J.tupleWidth - (I b.rev - 1)
  omega

/-- Determinant terms for the reflected, alphabet-reversed tuple network. -/
abbrev TupleFiniteFactorNetworkTerm {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :=
  FiniteFactorNetworkTerm (reverseFiniteEdreiData D)
    (tupleNetworkSource J) (tupleNetworkSink I J hstruct)

/-- Bounded vertex-disjoint path families for a tuple minor. -/
abbrev TupleVertexDisjointPathFamily {p q r : ℕ} (D : FiniteEdreiData p q)
    (I J : IncreasingIndexTuple r) (hstruct : StructurallyAdmissible I J) :=
  {T : TupleFiniteFactorNetworkTerm D I J hstruct // NetworkTermGood T}

theorem networkStepAllowed_eq_or_succ {p q N t : ℕ} {x y : Fin (N + 1)}
    (h : NetworkStepAllowed p q N t x y) :
    y.val = x.val ∨ y.val = x.val + 1 := by
  unfold NetworkStepAllowed at h
  split at h
  · exact h
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr h.2.2

theorem FiniteFactorPath.position_step_eq_or_succ
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount p q N)) :
    (P.position t.succ).val = (P.position t.castSucc).val ∨
      (P.position t.succ).val = (P.position t.castSucc).val + 1 :=
  networkStepAllowed_eq_or_succ (P.valid t)

theorem FiniteFactorPath.position_monotone
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    Monotone P.position := by
  rw [Fin.monotone_iff_le_succ]
  intro t
  have h := P.position_step_eq_or_succ t
  change (P.position t.castSucc).val ≤ (P.position t.succ).val
  omega

theorem FiniteFactorPath.source_le_position
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (s : Fin (finiteFactorStageCount p q N + 1)) :
    source ≤ P.position s := by
  calc
    source = P.position 0 := P.source_eq.symm
    _ ≤ P.position s := P.position_monotone (Fin.zero_le s)

theorem FiniteFactorPath.position_le_sink
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (s : Fin (finiteFactorStageCount p q N + 1)) :
    P.position s ≤ sink := by
  calc
    P.position s ≤ P.position (Fin.last _) := P.position_monotone (Fin.le_last s)
    _ = sink := P.sink_eq

theorem FiniteFactorPath.position_le_source_add_stage
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (s : Fin (finiteFactorStageCount p q N + 1)) :
    (P.position s).val ≤ source.val + s.val := by
  induction s using Fin.induction with
  | zero => simp [P.source_eq]
  | succ s ih =>
      have hstep := P.position_step_eq_or_succ s
      change (P.position s.succ).val ≤ source.val + s.succ.val
      change (P.position s.castSucc).val ≤ source.val + s.castSucc.val at ih
      change (P.position s.succ).val ≤ source.val + (s.val + 1)
      change (P.position s.castSucc).val ≤ source.val + s.val at ih
      omega

/-- A monotone unit-step path crosses every wire strictly between its endpoints exactly once. -/
theorem FiniteFactorPath.existsUnique_step_at_wire
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (k : ℕ) (hsource : source.val ≤ k) (hsink : k < sink.val) :
    ∃! t : Fin (finiteFactorStageCount p q N),
      (P.position t.castSucc).val = k ∧ (P.position t.succ).val = k + 1 := by
  let L := finiteFactorStageCount p q N
  let above : Finset (Fin (L + 1)) :=
    Finset.univ.filter fun s ↦ k < (P.position s).val
  have habove : above.Nonempty := by
    refine ⟨Fin.last L, ?_⟩
    simp only [above, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa [L, P.sink_eq] using hsink
  let s := above.min' habove
  have hsAbove : k < (P.position s).val := by
    have hsMem := above.min'_mem habove
    exact (Finset.mem_filter.mp hsMem).2
  have hsNe : s ≠ 0 := by
    intro hs
    have h := hsAbove
    rw [hs, P.source_eq] at h
    omega
  have hsPos : 0 < s.val := Nat.pos_of_ne_zero fun h ↦ hsNe (Fin.ext h)
  let t : Fin L := ⟨s.val - 1, by
    have hslt := s.isLt
    omega⟩
  have htSucc : t.succ = s := by
    apply Fin.ext
    simp [t]
    omega
  have htCast_lt : t.castSucc < s := by
    rw [← htSucc]
    exact Fin.castSucc_lt_succ
  have htNotAbove : ¬k < (P.position t.castSucc).val := by
    intro htAbove
    have htMem : t.castSucc ∈ above := by
      simp [above, htAbove]
    have hmin := above.min'_le t.castSucc htMem
    exact (not_le_of_gt htCast_lt) hmin
  have hstep := P.position_step_eq_or_succ t
  have htNext : k < (P.position t.succ).val := by simpa [htSucc] using hsAbove
  have htCross : (P.position t.castSucc).val = k ∧
      (P.position t.succ).val = k + 1 := by
    omega
  refine ⟨t, htCross, ?_⟩
  intro u hu
  apply Fin.ext
  by_contra hne
  by_cases htu : t.val < u.val
  · have hvertices : t.succ ≤ u.castSucc := htu
    have hmono := P.position_monotone hvertices
    change (P.position t.succ).val ≤ (P.position u.castSucc).val at hmono
    omega
  · have hut : u.val < t.val := by omega
    have hvertices : u.succ ≤ t.castSucc := hut
    have hmono := P.position_monotone hvertices
    change (P.position u.succ).val ≤ (P.position t.castSucc).val at hmono
    omega

/-- In a vertex-disjoint family whose sinks are strictly ordered, the paths have that same order
at every preceding stage. -/
theorem networkTermGood_position_lt_of_sink_strictMono
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (hsink : StrictMono sink)
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
      have hP := P.position_step_eq_or_succ t
      have hQ := Q.position_step_eq_or_succ t
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

/-- Every good reflected tuple-network term has the identity source permutation. -/
theorem tupleNetwork_good_perm_eq_refl
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (T : TupleFiniteFactorNetworkTerm D I J hstruct) (hgood : NetworkTermGood T) :
    T.1 = Equiv.refl (Fin r) := by
  apply Equiv.ext
  intro b
  have hmono : StrictMono T.1 := by
    intro a c hac
    have hpos := networkTermGood_position_lt_of_sink_strictMono
      (tupleNetworkSink_strictMono I J hstruct) T hgood hac 0
    rw [(T.2 a).source_eq, (T.2 c).source_eq] at hpos
    exact (tupleNetworkSource_strictMono J).lt_iff_lt.mp hpos
  let f : Fin r →o Fin r :=
    { toFun := T.1
      monotone' := hmono.monotone }
  have hf : f = OrderHom.id := OrderHom.eq_id_of_injective f hmono.injective
  exact DFunLike.congr_fun hf b

/-- A strictly increasing map on a finite interval grows at least by every finite offset. -/
theorem strictMono_fin_add_le {r : ℕ} {f : Fin r → ℕ}
    (hf : StrictMono f) (i : Fin r) (k : ℕ) (hbound : i.val + k < r) :
    k + f i ≤ f ⟨i.val + k, hbound⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk : i.val + k < r := by omega
      have hprev := ih hk
      have hstep :
          f ⟨i.val + k, hk⟩ < f ⟨i.val + (k + 1), hbound⟩ := by
        apply hf
        exact Fin.mk_lt_mk.mpr (by omega)
      omega

/-- A strictly increasing map on a finite interval grows by at least the index gap. -/
theorem strictMono_fin_gap {r : ℕ} {f : Fin r → ℕ} (hf : StrictMono f)
    {a b : Fin r} (hab : a ≤ b) :
    b.val - a.val + f a ≤ f b := by
  have hbound : a.val + (b.val - a.val) < r := by
    rw [Nat.add_sub_of_le hab]
    exact b.isLt
  have h := strictMono_fin_add_le hf a (b.val - a.val) hbound
  convert h using 1
  apply congrArg f
  apply Fin.ext
  exact (Nat.add_sub_of_le hab).symm

/-- The vertex separating the beta chips from the alpha blocks. -/
def betaBoundaryVertex (p q N : ℕ) : Fin (finiteFactorStageCount p q N + 1) :=
  ⟨q, by simp [finiteFactorStageCount]⟩

/-- Boundary after the first `i` alpha blocks. -/
def alphaBoundaryVertex (p q N : ℕ) (i : Fin (p + 1)) :
    Fin (finiteFactorStageCount p q N + 1) :=
  ⟨q + i.val * N, by
    simp only [finiteFactorStageCount]
    have hi := i.isLt
    have hi' : i.val ≤ p := by omega
    have hmul := Nat.mul_le_mul_right N hi'
    omega⟩

@[simp]
theorem alphaBoundaryVertex_zero (p q N : ℕ) :
    alphaBoundaryVertex p q N 0 = betaBoundaryVertex p q N := by
  apply Fin.ext
  simp [alphaBoundaryVertex, betaBoundaryVertex]

@[simp]
theorem alphaBoundaryVertex_last (p q N : ℕ) :
    alphaBoundaryVertex p q N (Fin.last p) =
      Fin.last (finiteFactorStageCount p q N) := by
  apply Fin.ext
  rfl

/-- A vertex inside alpha block `i`, after its first `k` adjacent chips. -/
def alphaBlockVertex (p q N : ℕ) (i : Fin p) (k : Fin (N + 1)) :
    Fin (finiteFactorStageCount p q N + 1) :=
  ⟨q + i.val * N + k.val, by
    simp only [finiteFactorStageCount]
    have hi := i.isLt
    have hk := k.isLt
    have hmul := Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hi)
    have hblock : i.val * N + N ≤ p * N := by
      simpa [Nat.succ_mul] using hmul
    omega⟩

/-- The elementary alpha stage at wire `k` in block `i`. -/
def alphaBlockStage (p q N : ℕ) (i : Fin p) (k : Fin N) :
    Fin (finiteFactorStageCount p q N) :=
  ⟨q + i.val * N + k.val, by
    simp only [finiteFactorStageCount]
    have hi := i.isLt
    have hk := k.isLt
    have hmul := Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hi)
    have hblock : i.val * N + N ≤ p * N := by
      simpa [Nat.succ_mul] using hmul
    omega⟩

@[simp]
theorem alphaBlockVertex_zero (p q N : ℕ) (i : Fin p) :
    alphaBlockVertex p q N i 0 = alphaBoundaryVertex p q N i.castSucc := by
  apply Fin.ext
  simp [alphaBlockVertex, alphaBoundaryVertex]

@[simp]
theorem alphaBlockVertex_last (p q N : ℕ) (i : Fin p) :
    alphaBlockVertex p q N i (Fin.last N) = alphaBoundaryVertex p q N i.succ := by
  apply Fin.ext
  simp [alphaBlockVertex, alphaBoundaryVertex, Nat.succ_mul, Nat.add_assoc]

@[simp]
theorem alphaBlockStage_castSucc (p q N : ℕ) (i : Fin p) (k : Fin N) :
    (alphaBlockStage p q N i k).castSucc =
      alphaBlockVertex p q N i k.castSucc := by
  rfl

@[simp]
theorem alphaBlockStage_succ (p q N : ℕ) (i : Fin p) (k : Fin N) :
    (alphaBlockStage p q N i k).succ = alphaBlockVertex p q N i k.succ := by
  rfl

/-- Before the chip at its current wire, a path cannot move inside an alpha block. -/
theorem FiniteFactorPath.position_alphaBlock_of_le_start
    {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (i : Fin p) (k : Fin (N + 1))
    (hk : k.val ≤ (P.position (alphaBlockVertex p q N i 0)).val) :
    P.position (alphaBlockVertex p q N i k) =
      P.position (alphaBlockVertex p q N i 0) := by
  apply Fin.ext
  induction k using Fin.induction with
  | zero => rfl
  | succ k ih =>
      have hklt : k.val <
          (P.position (alphaBlockVertex p q N i 0)).val := by
        have hs := hk
        change k.val + 1 ≤ (P.position (alphaBlockVertex p q N i 0)).val at hs
        omega
      have hvalid := P.valid (alphaBlockStage p q N i k)
      change NetworkStepAllowed p q N (q + i.val * N + k.val)
        (P.position (alphaBlockStage p q N i k).castSucc)
        (P.position (alphaBlockStage p q N i k).succ) at hvalid
      unfold NetworkStepAllowed at hvalid
      have hnotBeta : ¬q + i.val * N + k.val < q := by omega
      rw [if_neg hnotBeta] at hvalid
      rcases hvalid with hstay | hmove
      · change (P.position (alphaBlockVertex p q N i k.succ)).val =
          (P.position (alphaBlockVertex p q N i 0)).val
        change (P.position (alphaBlockStage p q N i k).succ).val =
          (P.position (alphaBlockVertex p q N i 0)).val
        rw [hstay]
        have hk' : k.castSucc.val ≤
            (P.position (alphaBlockVertex p q N i 0)).val := by
          change k.val ≤ _
          exact hklt.le
        simpa only [alphaBlockStage_castSucc] using ih hk'
      · have hN : 0 < N := Nat.pos_of_ne_zero fun hN ↦ by simpa [hN] using k.isLt
        have hsub : q + i.val * N + k.val - q = i.val * N + k.val := by omega
        have hdiv : (i.val * N + k.val) / N = i.val := by
          rw [Nat.mul_comm i.val N, Nat.mul_add_div hN, Nat.div_eq_of_lt k.isLt, add_zero]
        have hmod : (i.val * N + k.val) % N = k.val := by
          rw [Nat.mul_comm i.val N, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]
        rw [hsub, hdiv, hmod] at hmove
        have hcurrent :
            (P.position (alphaBlockStage p q N i k).castSucc).val =
              (P.position (alphaBlockVertex p q N i 0)).val := by
          have hk' : k.castSucc.val ≤
              (P.position (alphaBlockVertex p q N i 0)).val := by
            change k.val ≤ _
            exact hklt.le
          simpa only [alphaBlockStage_castSucc] using ih hk'
        rcases hmove with ⟨-, hx, -⟩
        rw [hcurrent] at hx
        omega

/-- The partition row encoded by a reflected wire at one network vertex. -/
def reflectedWirePart {r N : ℕ} (a : Fin r) (x : Fin (N + 1)) : ℕ :=
  N - (a.rev.val + x.val)

theorem reflectedWirePart_antitone_of_strictMono
    {r N : ℕ} {x : Fin r → Fin (N + 1)} (hx : StrictMono x) :
    Antitone (fun a ↦ reflectedWirePart a (x a)) := by
  intro a b hab
  have hgap := strictMono_fin_gap (fun _ _ h ↦ hx h) hab
  have harev : a.rev.val + a.val + 1 = r := by
    change r - (a.val + 1) + a.val + 1 = r
    omega
  have hbrev : b.rev.val + b.val + 1 = r := by
    change r - (b.val + 1) + b.val + 1 = r
    omega
  unfold reflectedWirePart
  apply Nat.sub_le_sub_left
  omega

theorem reflectedWirePart_source {r : ℕ} (J : IncreasingIndexTuple r) (a : Fin r) :
    reflectedWirePart a (tupleNetworkSource J a) =
      containingOuterPartition J a := by
  change J.tupleWidth -
      (a.rev.val + (J.tupleWidth - (J a.rev - 1))) =
    J a.rev - (a.rev.val + 1)
  have hJ := J.value_le_tupleWidth a.rev
  have hpos := J.position_le a.rev
  omega

theorem reflectedWirePart_sink {r : ℕ} (I J : IncreasingIndexTuple r)
    (hstruct : StructurallyAdmissible I J) (a : Fin r) :
    reflectedWirePart a (tupleNetworkSink I J hstruct a) =
      containedInnerPartition I J hstruct a := by
  change J.tupleWidth -
      (a.rev.val + (J.tupleWidth - (I a.rev - 1))) =
    I a.rev - (a.rev.val + 1)
  have hI := (hstruct a.rev).trans (J.value_le_tupleWidth a.rev)
  have hpos := I.position_le a.rev
  omega

/-- The intermediate partition read at the beta/alpha boundary of a disjoint family. -/
def TupleVertexDisjointPathFamily.intermediate
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct) :
    IntermediateRectanglePartition
      (containedInnerPartition I J hstruct) (containingOuterPartition J) where
  middle :=
    { rowLength := fun a ↦
        ⟨reflectedWirePart a ((F.1.2 a).position
          (betaBoundaryVertex p q J.tupleWidth)),
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
      antitone := reflectedWirePart_antitone_of_strictMono (by
        intro a b hab
        exact networkTermGood_position_lt_of_sink_strictMono
          (tupleNetworkSink_strictMono I J hstruct) F.1 F.2 hab
          (betaBoundaryVertex p q J.tupleWidth)) }
  inner_le := by
    intro a
    rw [← reflectedWirePart_sink I J hstruct a]
    change reflectedWirePart a (tupleNetworkSink I J hstruct a) ≤
      reflectedWirePart a ((F.1.2 a).position
        (betaBoundaryVertex p q J.tupleWidth))
    unfold reflectedWirePart
    have hle := (F.1.2 a).position_le_sink (betaBoundaryVertex p q J.tupleWidth)
    change ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val ≤
      (tupleNetworkSink I J hstruct a).val at hle
    omega
  outer_ge := by
    intro a
    rw [← reflectedWirePart_source J a]
    change reflectedWirePart a ((F.1.2 a).position
        (betaBoundaryVertex p q J.tupleWidth)) ≤
      reflectedWirePart a (tupleNetworkSource J a)
    unfold reflectedWirePart
    have hle := (F.1.2 a).source_le_position (betaBoundaryVertex p q J.tupleWidth)
    have hsource : (tupleNetworkSource J a).val ≤
        (tupleNetworkSource J (F.1.1 a)).val := by
      rw [tupleNetwork_good_perm_eq_refl F.1 F.2]
      simp
    change (tupleNetworkSource J (F.1.1 a)).val ≤
      ((F.1.2 a).position (betaBoundaryVertex p q J.tupleWidth)).val at hle
    omega

/-- During one alpha block, an earlier path finishes strictly below a later path's starting
vertex.  This is the local interlacing relation behind the alpha column bound. -/
theorem TupleVertexDisjointPathFamily.alphaBlock_separated
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (i : Fin p) {a b : Fin r} (hab : a < b) :
    (F.1.2 a).position (alphaBlockVertex p q J.tupleWidth i (Fin.last J.tupleWidth)) <
      (F.1.2 b).position (alphaBlockVertex p q J.tupleWidth i 0) := by
  let N := J.tupleWidth
  let P := F.1.2 a
  let Q := F.1.2 b
  let vStart := alphaBlockVertex p q N i 0
  let vEnd := alphaBlockVertex p q N i (Fin.last N)
  have hstart : P.position vStart < Q.position vStart :=
    networkTermGood_position_lt_of_sink_strictMono
      (tupleNetworkSink_strictMono I J hstruct) F.1 F.2 hab vStart
  by_contra hnot
  have hend : (Q.position vStart).val ≤ (P.position vEnd).val := by
    change ¬(P.position vEnd).val < (Q.position vStart).val at hnot
    omega
  have hqpos : 0 < (Q.position vStart).val := by
    change (P.position vStart).val < (Q.position vStart).val at hstart
    omega
  let k := (Q.position vStart).val - 1
  have hkQ : k + 1 = (Q.position vStart).val := by
    dsimp only [k]
    omega
  have hsource : (tupleNetworkSource J (F.1.1 a)).val ≤ k := by
    have hs := P.source_le_position vStart
    change (tupleNetworkSource J (F.1.1 a)).val ≤ (P.position vStart).val at hs
    change (P.position vStart).val < (Q.position vStart).val at hstart
    dsimp only [k]
    omega
  have hsink : k < (tupleNetworkSink I J hstruct a).val := by
    have he := P.position_le_sink vEnd
    change (P.position vEnd).val ≤ (tupleNetworkSink I J hstruct a).val at he
    dsimp only [k]
    omega
  obtain ⟨t, ht, -⟩ := P.existsUnique_step_at_wire k hsource hsink
  have htLower : vStart.val ≤ t.val := by
    by_contra hbad
    have hvertex : t.succ ≤ vStart := by
      change t.val + 1 ≤ vStart.val
      omega
    have hmono := P.position_monotone hvertex
    change (P.position t.succ).val ≤ (P.position vStart).val at hmono
    change (P.position vStart).val < (Q.position vStart).val at hstart
    omega
  have htUpper : t.val < vEnd.val := by
    by_contra hbad
    have hvertex : vEnd ≤ t.castSucc := by
      change vEnd.val ≤ t.val
      omega
    have hmono := P.position_monotone hvertex
    change (P.position vEnd).val ≤ (P.position t.castSucc).val at hmono
    omega
  have hN : 0 < N := by
    have hposlt := (Q.position vStart).isLt
    change (Q.position vStart).val < N + 1 at hposlt
    omega
  have htLower' : q + i.val * N ≤ t.val := by
    simpa only [vStart, alphaBlockVertex] using htLower
  have htUpper' : t.val < q + i.val * N + N := by
    change t.val < q + i.val * N + N at htUpper
    exact htUpper
  have hq : q ≤ t.val := by
    omega
  have huLower : i.val * N ≤ t.val - q := by
    apply Nat.le_sub_of_add_le
    simpa [Nat.add_comm] using htLower'
  have huUpper : t.val - q < (i.val + 1) * N := by
    rw [Nat.add_mul]
    omega
  have hdiv : (t.val - q) / N = i.val := by
    exact Nat.div_eq_of_lt_le (by simpa [Nat.mul_comm] using huLower)
      (by simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using huUpper)
  have hvalid := P.valid t
  unfold NetworkStepAllowed at hvalid
  rw [if_neg (not_lt_of_ge hq)] at hvalid
  rcases hvalid with hstay | hmove
  · omega
  · have hx : (P.position t.castSucc).val = (t.val - q) % N := hmove.2.1
    have hmod : (t.val - q) % N = k := by omega
    have htStage : t.val = q + i.val * N + k := by
      calc
        t.val = q + (t.val - q) := (Nat.add_sub_of_le hq).symm
        _ = q + ((t.val - q) / N * N + (t.val - q) % N) := by
          rw [Nat.mul_comm ((t.val - q) / N) N, Nat.div_add_mod]
        _ = q + i.val * N + k := by rw [hdiv, hmod, Nat.add_assoc]
    have hkN : k < N := by
      have hklt := (Q.position vStart).isLt
      dsimp only [k, N] at hklt ⊢
      omega
    let kFin : Fin N := ⟨k, hkN⟩
    have htEq : t = alphaBlockStage p q N i kFin := by
      apply Fin.ext
      exact htStage
    have hPcollision : P.position t.succ = Q.position t.succ := by
      apply Fin.ext
      let qwire : Fin (N + 1) :=
        ⟨(Q.position vStart).val, (Q.position vStart).isLt⟩
      have hQstay := Q.position_alphaBlock_of_le_start i qwire (by
        dsimp only [qwire, vStart]
        exact le_rfl)
      have hvertex : alphaBlockVertex p q N i qwire = t.succ := by
        apply Fin.ext
        change q + i.val * N + (Q.position vStart).val = t.val + 1
        omega
      calc
        (P.position t.succ).val = (Q.position vStart).val := by omega
        _ = (Q.position (alphaBlockVertex p q N i qwire)).val := by
          rw [hQstay]
        _ = (Q.position t.succ).val := by rw [hvertex]
    exact F.2 a b hab t.succ hPcollision

/-- Iterating the one-block interlacing relation compares the final alpha endpoint in one row
with the beta-boundary endpoint `n` rows below it. -/
theorem TupleVertexDisjointPathFamily.alphaBoundary_chain
    {p q r : ℕ} {D : FiniteEdreiData p q}
    {I J : IncreasingIndexTuple r} {hstruct : StructurallyAdmissible I J}
    (F : TupleVertexDisjointPathFamily D I J hstruct)
    (a : Fin r) (n : ℕ) (hn : n ≤ p) (hr : a.val + n < r) :
    n + ((F.1.2 a).position
        (alphaBoundaryVertex p q J.tupleWidth (Fin.last p))).val ≤
      ((F.1.2 ⟨a.val + n, hr⟩).position
        (alphaBoundaryVertex p q J.tupleWidth
          ⟨p - n, Nat.lt_succ_of_le (Nat.sub_le p n)⟩)).val := by
  induction n with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero, Nat.sub_zero]
      have ha : (⟨a.val, hr⟩ : Fin r) = a := by
        apply Fin.ext
        rfl
      have hp : (⟨p, Nat.lt_succ_of_le (Nat.sub_le p 0)⟩ : Fin (p + 1)) =
          Fin.last p := by
        apply Fin.ext
        simp
      rw [ha, hp]
  | succ n ih =>
      have hn' : n ≤ p := by omega
      have hr' : a.val + n < r := by omega
      have hchain := ih hn' hr'
      let c : Fin r := ⟨a.val + n, hr'⟩
      let d : Fin r := ⟨a.val + (n + 1), hr⟩
      have hcd : c < d := by
        change a.val + n < a.val + (n + 1)
        omega
      let iblock : Fin p := ⟨p - (n + 1), by omega⟩
      have hsep := F.alphaBlock_separated iblock hcd
      have hleftVertex :
          alphaBlockVertex p q J.tupleWidth iblock (Fin.last J.tupleWidth) =
            alphaBoundaryVertex p q J.tupleWidth
              ⟨p - n, Nat.lt_succ_of_le (Nat.sub_le p n)⟩ := by
        rw [alphaBlockVertex_last]
        apply Fin.ext
        have hiblock : iblock.succ.val = p - n := by
          change (p - (n + 1)) + 1 = p - n
          omega
        change q + iblock.succ.val * J.tupleWidth =
          q + (p - n) * J.tupleWidth
        rw [hiblock]
      have hrightVertex :
          alphaBlockVertex p q J.tupleWidth iblock 0 =
            alphaBoundaryVertex p q J.tupleWidth
              ⟨p - (n + 1), Nat.lt_succ_of_le (Nat.sub_le p (n + 1))⟩ := by
        rw [alphaBlockVertex_zero]
        apply Fin.ext
        rfl
      rw [hleftVertex, hrightVertex] at hsep
      change ((F.1.2 c).position
          (alphaBoundaryVertex p q J.tupleWidth
            ⟨p - n, Nat.lt_succ_of_le (Nat.sub_le p n)⟩)).val <
        ((F.1.2 d).position
          (alphaBoundaryVertex p q J.tupleWidth
            ⟨p - (n + 1), Nat.lt_succ_of_le (Nat.sub_le p (n + 1))⟩)).val at hsep
      change n + ((F.1.2 a).position
          (alphaBoundaryVertex p q J.tupleWidth (Fin.last p))).val ≤
        ((F.1.2 c).position
          (alphaBoundaryVertex p q J.tupleWidth
            ⟨p - n, Nat.lt_succ_of_le (Nat.sub_le p n)⟩)).val at hchain
      change n + 1 + ((F.1.2 a).position
          (alphaBoundaryVertex p q J.tupleWidth (Fin.last p))).val ≤
        ((F.1.2 d).position
          (alphaBoundaryVertex p q J.tupleWidth
            ⟨p - (n + 1), Nat.lt_succ_of_le (Nat.sub_le p (n + 1))⟩)).val
      omega

end

end ToeplitzPositroids.Edrei
