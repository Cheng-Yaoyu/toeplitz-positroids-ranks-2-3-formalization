import ToeplitzPositroids.RankThree.ConvexChainCriterion
import Lean.Elab.Tactic.Omega

/-!
# Maximal collinear intervals in the simplified moment chain

Under the convex-chain criterion, collinear triples are controlled by maximal
constant runs of consecutive edge slopes.  This file packages those runs as
closed vertex intervals, proves their elementary intersection properties, and
relates them to dependent triples and row rank.
-/

namespace ToeplitzPositroids.RankThree

open Matrix Set

noncomputable section

variable {n : ℕ} {A : Matrix (Fin 3) (Fin n) ℝ}

/-- A maximal nontrivial constant-slope run, recorded as its closed interval of vertices.
The interval contains at least three vertices because `start + 2 ≤ stop`. -/
structure MaximalConstantSlopeInterval (A : Matrix (Fin 3) (Fin n) ℝ) where
  /-- The first vertex in the run. -/
  start : ℕ
  /-- The last vertex in the run. -/
  stop : ℕ
  nontrivial : start + 2 ≤ stop
  stop_lt : stop < simplificationSize A
  constant : SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) start stop
  maximal : ∀ {a b : ℕ}, a ≤ start → stop ≤ b → b < simplificationSize A →
    SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) a b →
      a = start ∧ b = stop

namespace MaximalConstantSlopeInterval

/-- The set of natural-number vertex indices belonging to a maximal run. -/
def vertices (I : MaximalConstantSlopeInterval A) : Set ℕ :=
  Set.Icc I.start I.stop

@[simp]
theorem mem_vertices {I : MaximalConstantSlopeInterval A} {i : ℕ} :
    i ∈ I.vertices ↔ I.start ≤ i ∧ i ≤ I.stop :=
  Iff.rfl

/-- Every maximal nontrivial run contains at least three vertices. -/
theorem three_le_vertexCount (I : MaximalConstantSlopeInterval A) :
    3 ≤ I.stop - I.start + 1 := by
  have h := I.nontrivial
  omega

/-- A maximal run contains its two endpoints. -/
theorem endpoints_mem (I : MaximalConstantSlopeInterval A) :
    I.start ∈ I.vertices ∧ I.stop ∈ I.vertices := by
  have hle : I.start ≤ I.stop := by
    have h := I.nontrivial
    omega
  exact ⟨⟨le_rfl, hle⟩, ⟨hle, le_rfl⟩⟩

/-- Two maximal intervals with the same endpoints are equal. -/
@[ext]
theorem ext {I J : MaximalConstantSlopeInterval A}
    (hstart : I.start = J.start) (hstop : I.stop = J.stop) : I = J := by
  cases I
  cases J
  simp_all

private theorem eq_of_two_common_vertices_of_start_le
    {I J : MaximalConstantSlopeInterval A} {x y : ℕ}
    (hstart : I.start ≤ J.start) (hxI : x ∈ I.vertices) (hxJ : x ∈ J.vertices)
    (hyI : y ∈ I.vertices) (hyJ : y ∈ J.vertices) (hxy : x < y) :
    I = J := by
  have hxI' := mem_vertices.mp hxI
  have hxJ' := mem_vertices.mp hxJ
  have hxiStop : x < I.stop := lt_of_lt_of_le hxy (mem_vertices.mp hyI).2
  have hxjStop : x < J.stop := lt_of_lt_of_le hxy (mem_vertices.mp hyJ).2
  have hbase :
      edgeSlope (simplifiedMomentU A) (simplifiedMomentV A) J.start =
        edgeSlope (simplifiedMomentU A) (simplifiedMomentV A) I.start := by
    have hI := I.constant hxI'.1 hxiStop
    have hJ := J.constant hxJ'.1 hxjStop
    exact hJ.symm.trans hI
  by_cases hstop : I.stop ≤ J.stop
  · have hunion :
        SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A)
          I.start J.stop := by
      intro t hit htstop
      by_cases htI : t < I.stop
      · exact I.constant hit htI
      · have hJt : J.start ≤ t := by
          have hJx : J.start ≤ x := hxJ'.1
          have hxIstop : x ≤ I.stop := hxI'.2
          have hIstopT : I.stop ≤ t := Nat.le_of_not_gt htI
          exact hJx.trans (hxIstop.trans hIstopT)
        exact (J.constant hJt htstop).trans hbase
    have hImax := I.maximal le_rfl hstop J.stop_lt hunion
    have hJmax := J.maximal hstart le_rfl J.stop_lt hunion
    exact ext hJmax.1 hImax.2.symm
  · have hstop' : J.stop ≤ I.stop := (lt_of_not_ge hstop).le
    have hJmax := J.maximal hstart hstop' I.stop_lt I.constant
    exact ext hJmax.1 hJmax.2

/-- If two maximal constant-slope intervals share two distinct vertices, then the intervals
are equal. -/
theorem eq_of_two_common_vertices
    {I J : MaximalConstantSlopeInterval A} {x y : ℕ}
    (hxI : x ∈ I.vertices) (hxJ : x ∈ J.vertices)
    (hyI : y ∈ I.vertices) (hyJ : y ∈ J.vertices) (hxy : x ≠ y) :
    I = J := by
  rcases lt_or_gt_of_ne hxy with hxy | hyx
  · by_cases hstart : I.start ≤ J.start
    · exact eq_of_two_common_vertices_of_start_le hstart hxI hxJ hyI hyJ hxy
    · exact (eq_of_two_common_vertices_of_start_le (lt_of_not_ge hstart).le
        hxJ hxI hyJ hyI hxy).symm
  · by_cases hstart : I.start ≤ J.start
    · exact eq_of_two_common_vertices_of_start_le hstart hyI hyJ hxI hxJ hyx
    · exact (eq_of_two_common_vertices_of_start_le (lt_of_not_ge hstart).le
        hyJ hyI hxJ hxI hyx).symm

/-- Distinct maximal intervals have at most one common vertex. -/
theorem common_vertices_eq_of_ne {I J : MaximalConstantSlopeInterval A} (hne : I ≠ J)
    {x y : ℕ} (hxI : x ∈ I.vertices) (hxJ : x ∈ J.vertices)
    (hyI : y ∈ I.vertices) (hyJ : y ∈ J.vertices) :
    x = y := by
  by_contra hxy
  exact hne (eq_of_two_common_vertices hxI hxJ hyI hyJ hxy)

/-- If two distinct maximal intervals meet, their common vertex is an endpoint of each: the
last vertex of one interval and the first vertex of the other. -/
theorem common_vertex_is_common_endpoint {I J : MaximalConstantSlopeInterval A} (hne : I ≠ J)
    {x : ℕ} (hxI : x ∈ I.vertices) (hxJ : x ∈ J.vertices) :
    (x = I.stop ∧ x = J.start) ∨ (x = J.stop ∧ x = I.start) := by
  by_cases hstart : I.start ≤ J.start
  · have hJI : J.start ≤ I.stop := (mem_vertices.mp hxJ).1.trans (mem_vertices.mp hxI).2
    have hEq : J.start = I.stop := by
      apply le_antisymm hJI
      apply le_of_not_gt
      intro hlt
      have hJnext : J.start + 1 ≤ J.stop := by
        have h := J.nontrivial
        omega
      have hInext : J.start + 1 ≤ I.stop := by omega
      have hJstartI : J.start ∈ I.vertices := ⟨hstart, hJI⟩
      have hJstartJ : J.start ∈ J.vertices := (endpoints_mem J).1
      have hnextI : J.start + 1 ∈ I.vertices := ⟨hstart.trans (Nat.le_add_right _ _), hInext⟩
      have hnextJ : J.start + 1 ∈ J.vertices :=
        ⟨Nat.le_add_right _ _, hJnext⟩
      exact hne (eq_of_two_common_vertices hJstartI hJstartJ hnextI hnextJ (by omega))
    left
    have hxStop : x = I.stop := le_antisymm (mem_vertices.mp hxI).2 (by
      rw [← hEq]
      exact (mem_vertices.mp hxJ).1)
    exact ⟨hxStop, hxStop.trans hEq.symm⟩
  · have hstart' : J.start ≤ I.start := (lt_of_not_ge hstart).le
    have hIJ : I.start ≤ J.stop := (mem_vertices.mp hxI).1.trans (mem_vertices.mp hxJ).2
    have hEq : I.start = J.stop := by
      apply le_antisymm hIJ
      apply le_of_not_gt
      intro hlt
      have hInext : I.start + 1 ≤ I.stop := by
        have h := I.nontrivial
        omega
      have hJnext : I.start + 1 ≤ J.stop := by omega
      have hIstartI : I.start ∈ I.vertices := (endpoints_mem I).1
      have hIstartJ : I.start ∈ J.vertices := ⟨hstart', hIJ⟩
      have hnextI : I.start + 1 ∈ I.vertices :=
        ⟨Nat.le_add_right _ _, hInext⟩
      have hnextJ : I.start + 1 ∈ J.vertices :=
        ⟨hstart'.trans (Nat.le_add_right _ _), hJnext⟩
      exact hne (eq_of_two_common_vertices hIstartI hIstartJ hnextI hnextJ (by omega))
    right
    have hxStop : x = J.stop := le_antisymm (mem_vertices.mp hxJ).2 (by
      rw [← hEq]
      exact (mem_vertices.mp hxI).1)
    exact ⟨hxStop, hxStop.trans hEq.symm⟩

end MaximalConstantSlopeInterval

/-- The valid edges whose slope agrees with the slope of edge `e`. -/
def equalSlopeEdges (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (simplificationSize A)).filter fun t ↦
    t + 1 < simplificationSize A ∧ simplifiedEdgeSlope A t = simplifiedEdgeSlope A e

@[simp]
theorem mem_equalSlopeEdges {e t : ℕ} :
    t ∈ equalSlopeEdges A e ↔
      t + 1 < simplificationSize A ∧ simplifiedEdgeSlope A t = simplifiedEdgeSlope A e := by
  classical
  simp only [equalSlopeEdges, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, ht⟩
    exact ht
  · intro ht
    exact ⟨by omega, ht⟩

theorem equalSlopeEdges_nonempty (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ)
    (he : e + 1 < simplificationSize A) :
    (equalSlopeEdges A e).Nonempty := by
  exact ⟨e, mem_equalSlopeEdges.mpr ⟨he, rfl⟩⟩

/-- The first edge in the maximal equality class of the valid edge `e`. -/
def equalSlopeRunStart (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ)
    (he : e + 1 < simplificationSize A) : ℕ :=
  (equalSlopeEdges A e).min' (equalSlopeEdges_nonempty A e he)

/-- The last edge in the maximal equality class of the valid edge `e`. -/
def equalSlopeRunLastEdge (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ)
    (he : e + 1 < simplificationSize A) : ℕ :=
  (equalSlopeEdges A e).max' (equalSlopeEdges_nonempty A e he)

theorem equalSlopeRunStart_mem (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ)
    (he : e + 1 < simplificationSize A) :
    equalSlopeRunStart A e he ∈ equalSlopeEdges A e :=
  Finset.min'_mem _ _

theorem equalSlopeRunLastEdge_mem (A : Matrix (Fin 3) (Fin n) ℝ) (e : ℕ)
    (he : e + 1 < simplificationSize A) :
    equalSlopeRunLastEdge A e he ∈ equalSlopeEdges A e :=
  Finset.max'_mem _ _

theorem equalSlopeRunStart_le {e t : ℕ} (he : e + 1 < simplificationSize A)
    (ht : t ∈ equalSlopeEdges A e) :
    equalSlopeRunStart A e he ≤ t :=
  Finset.min'_le _ t ht

theorem le_equalSlopeRunLastEdge {e t : ℕ} (he : e + 1 < simplificationSize A)
    (ht : t ∈ equalSlopeEdges A e) :
    t ≤ equalSlopeRunLastEdge A e he :=
  Finset.le_max' _ t ht

/-- Monotone slopes make every edge between the extreme equal-slope edges have that same
slope. -/
theorem equalSlopeRun_constant (hSlopes : SimplifiedSlopesMonotone A) (e : ℕ)
    (he : e + 1 < simplificationSize A) :
    SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A)
      (equalSlopeRunStart A e he) (equalSlopeRunLastEdge A e he + 1) := by
  intro t hstart htlast
  have hlastMem := equalSlopeRunLastEdge_mem A e he
  have hstartMem := equalSlopeRunStart_mem A e he
  have ht_le : t ≤ equalSlopeRunLastEdge A e he := by omega
  have htValid : t + 1 < simplificationSize A := by
    have := (mem_equalSlopeEdges.mp hlastMem).1
    omega
  have hleStart := hSlopes hstart htValid
  have hleLast := hSlopes ht_le (mem_equalSlopeEdges.mp hlastMem).1
  change simplifiedEdgeSlope A (equalSlopeRunStart A e he) ≤
    simplifiedEdgeSlope A t at hleStart
  change simplifiedEdgeSlope A t ≤
    simplifiedEdgeSlope A (equalSlopeRunLastEdge A e he) at hleLast
  change simplifiedEdgeSlope A t = simplifiedEdgeSlope A (equalSlopeRunStart A e he)
  apply le_antisymm
  · calc
      simplifiedEdgeSlope A t ≤ simplifiedEdgeSlope A (equalSlopeRunLastEdge A e he) :=
        hleLast
      _ = simplifiedEdgeSlope A e := (mem_equalSlopeEdges.mp hlastMem).2
      _ = simplifiedEdgeSlope A (equalSlopeRunStart A e he) :=
        (mem_equalSlopeEdges.mp hstartMem).2.symm
  · exact hleStart

/-- The maximal nontrivial run generated by two consecutive equal edge slopes. -/
def maximalConstantSlopeIntervalOfEdge (hSlopes : SimplifiedSlopesMonotone A) (e : ℕ)
    (he : e + 2 < simplificationSize A)
    (heq : simplifiedEdgeSlope A (e + 1) = simplifiedEdgeSlope A e) :
    MaximalConstantSlopeInterval A := by
  have heValid : e + 1 < simplificationSize A := by omega
  let s := equalSlopeRunStart A e heValid
  let l := equalSlopeRunLastEdge A e heValid
  have heMem : e ∈ equalSlopeEdges A e := mem_equalSlopeEdges.mpr ⟨heValid, rfl⟩
  have heNextMem : e + 1 ∈ equalSlopeEdges A e :=
    mem_equalSlopeEdges.mpr ⟨he, heq⟩
  have hsle : s ≤ e := equalSlopeRunStart_le heValid heMem
  have hele : e + 1 ≤ l := le_equalSlopeRunLastEdge heValid heNextMem
  have hlMem : l ∈ equalSlopeEdges A e := equalSlopeRunLastEdge_mem A e heValid
  have hsMem : s ∈ equalSlopeEdges A e := equalSlopeRunStart_mem A e heValid
  have hlValid : l + 1 < simplificationSize A := (mem_equalSlopeEdges.mp hlMem).1
  refine
    { start := s
      stop := l + 1
      nontrivial := by omega
      stop_lt := hlValid
      constant := equalSlopeRun_constant hSlopes e heValid
      maximal := ?_ }
  intro a b has hlb hb hconstant
  have hsltb : s < b := by omega
  have hSlopeA : simplifiedEdgeSlope A a = simplifiedEdgeSlope A e := by
    have hsa := hconstant has hsltb
    change simplifiedEdgeSlope A s = simplifiedEdgeSlope A a at hsa
    exact hsa.symm.trans (mem_equalSlopeEdges.mp hsMem).2
  have haValid : a + 1 < simplificationSize A := by omega
  have haMem : a ∈ equalSlopeEdges A e := mem_equalSlopeEdges.mpr ⟨haValid, hSlopeA⟩
  have hsa : s ≤ a := equalSlopeRunStart_le heValid haMem
  have haEq : a = s := le_antisymm has hsa
  have hbEq : b = l + 1 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hlt
      have htValid : (l + 1) + 1 < simplificationSize A := by omega
      have hSlopeNext : simplifiedEdgeSlope A (l + 1) = simplifiedEdgeSlope A e := by
        have hnext := hconstant (by omega) hlt
        change simplifiedEdgeSlope A (l + 1) = simplifiedEdgeSlope A a at hnext
        exact hnext.trans hSlopeA
      have hnextMem : l + 1 ∈ equalSlopeEdges A e :=
        mem_equalSlopeEdges.mpr ⟨htValid, hSlopeNext⟩
      have := le_equalSlopeRunLastEdge heValid hnextMem
      omega
    · exact hlb
  exact ⟨haEq, hbEq⟩

@[simp]
theorem maximalConstantSlopeIntervalOfEdge_start
    (hSlopes : SimplifiedSlopesMonotone A) (e : ℕ)
    (he : e + 2 < simplificationSize A)
    (heq : simplifiedEdgeSlope A (e + 1) = simplifiedEdgeSlope A e) :
    (maximalConstantSlopeIntervalOfEdge hSlopes e he heq).start =
      equalSlopeRunStart A e (by omega) :=
  rfl

@[simp]
theorem maximalConstantSlopeIntervalOfEdge_stop
    (hSlopes : SimplifiedSlopesMonotone A) (e : ℕ)
    (he : e + 2 < simplificationSize A)
    (heq : simplifiedEdgeSlope A (e + 1) = simplifiedEdgeSlope A e) :
    (maximalConstantSlopeIntervalOfEdge hSlopes e he heq).stop =
      equalSlopeRunLastEdge A e (by omega) + 1 :=
  rfl

/-- Every constant-slope triple of vertices is contained in a unique maximal nontrivial run. -/
theorem existsUnique_maximalConstantSlopeInterval_of_constantBetween
    (hSlopes : SimplifiedSlopesMonotone A) {i j k : ℕ}
    (hij : i < j) (hjk : j < k) (hk : k < simplificationSize A)
    (hconstant : SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) i k) :
    ∃! I : MaximalConstantSlopeInterval A,
      i ∈ I.vertices ∧ j ∈ I.vertices ∧ k ∈ I.vertices := by
  have hiTwo : i + 2 < simplificationSize A := by omega
  have hiValid : i + 1 < simplificationSize A := by omega
  have hiOneK : i + 1 < k := by omega
  have heq := hconstant (by omega : i ≤ i + 1) hiOneK
  change simplifiedEdgeSlope A (i + 1) = simplifiedEdgeSlope A i at heq
  let I := maximalConstantSlopeIntervalOfEdge hSlopes i hiTwo heq
  have hiMem : i ∈ equalSlopeEdges A i := mem_equalSlopeEdges.mpr ⟨hiValid, rfl⟩
  have hstarti : equalSlopeRunStart A i hiValid ≤ i :=
    equalSlopeRunStart_le hiValid hiMem
  have hkPos : 0 < k := by omega
  have hkPredLt : k - 1 < k := by omega
  have hiPred : i ≤ k - 1 := by omega
  have hkPredSlope := hconstant hiPred hkPredLt
  change simplifiedEdgeSlope A (k - 1) = simplifiedEdgeSlope A i at hkPredSlope
  have hkPredMem : k - 1 ∈ equalSlopeEdges A i := by
    apply mem_equalSlopeEdges.mpr
    constructor
    · omega
    · exact hkPredSlope
  have hkLast : k - 1 ≤ equalSlopeRunLastEdge A i hiValid :=
    le_equalSlopeRunLastEdge hiValid hkPredMem
  have hikBounds :
      equalSlopeRunStart A i hiValid ≤ i ∧
        k ≤ equalSlopeRunLastEdge A i hiValid + 1 := by
    constructor
    · exact hstarti
    · omega
  have hiI : i ∈ I.vertices := by
    change equalSlopeRunStart A i hiValid ≤ i ∧
      i ≤ equalSlopeRunLastEdge A i hiValid + 1
    exact ⟨hikBounds.1, by omega⟩
  have hjI : j ∈ I.vertices := by
    change equalSlopeRunStart A i hiValid ≤ j ∧
      j ≤ equalSlopeRunLastEdge A i hiValid + 1
    exact ⟨hikBounds.1.trans hij.le, hjk.le.trans hikBounds.2⟩
  have hkI : k ∈ I.vertices := by
    change equalSlopeRunStart A i hiValid ≤ k ∧
      k ≤ equalSlopeRunLastEdge A i hiValid + 1
    exact ⟨hikBounds.1.trans (hij.trans hjk).le, hikBounds.2⟩
  refine ⟨I, ⟨hiI, hjI, hkI⟩, ?_⟩
  intro J hJ
  exact MaximalConstantSlopeInterval.eq_of_two_common_vertices
    hJ.1 hiI hJ.2.2 hkI (by omega)

/-- Under the convexity condition, a triple of distinct simplified classes is dependent
exactly when its three vertices lie in a unique maximal constant-slope interval. -/
theorem orderedMinor_simplified_eq_zero_iff_existsUnique_maximalInterval
    (hA : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    {p q r : Fin (simplificationSize A)} (hpq : p < q) (hqr : q < r) :
    orderedMinor (simplifiedMatrix A) (allRows 3)
        (selectedTripleEmbedding p q r hpq hqr) = 0 ↔
      ∃! I : MaximalConstantSlopeInterval A,
        p.val ∈ I.vertices ∧ q.val ∈ I.vertices ∧ r.val ∈ I.vertices := by
  constructor
  · intro hzero
    have hconstant :
        SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) p.val r.val :=
      (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hA hSlopes hpq hqr).mp hzero
    exact existsUnique_maximalConstantSlopeInterval_of_constantBetween hSlopes
      (by simpa using hpq) (by simpa using hqr) r.isLt hconstant
  · rintro ⟨I, ⟨hpI, hqI, hrI⟩, _⟩
    apply (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hA hSlopes hpq hqr).mpr
    intro t hpt htr
    have hstartP : I.start ≤ p.val := (MaximalConstantSlopeInterval.mem_vertices.mp hpI).1
    have hrStop : r.val ≤ I.stop := (MaximalConstantSlopeInterval.mem_vertices.mp hrI).2
    have ht := I.constant (hstartP.trans hpt) (htr.trans_le hrStop)
    have hpqNat : p.val < q.val := by simpa using hpq
    have hqrNat : q.val < r.val := by simpa using hqr
    have hpStop : p.val < I.stop := (hpqNat.trans hqrNat).trans_le hrStop
    have hp := I.constant hstartP hpStop
    exact ht.trans hp.symm

/-- The same unique-interval criterion for an arbitrary original triple in three distinct
nonloop simplification classes. -/
theorem orderedMinor_selectedTriple_eq_zero_iff_existsUnique_maximalInterval
    (hA : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    {i j k : Fin n} (hij : i < j) (hjk : j < k)
    (hi : ¬IsLoop A i) (hj : ¬IsLoop A j) (hk : ¬IsLoop A k)
    (hijClass : simplificationClassIndex A i hi ≠ simplificationClassIndex A j hj)
    (hjkClass : simplificationClassIndex A j hj ≠ simplificationClassIndex A k hk) :
    orderedMinor A (allRows 3) (selectedTripleEmbedding i j k hij hjk) = 0 ↔
      ∃! I : MaximalConstantSlopeInterval A,
        (simplificationClassIndex A i hi).val ∈ I.vertices ∧
        (simplificationClassIndex A j hj).val ∈ I.vertices ∧
        (simplificationClassIndex A k hk).val ∈ I.vertices := by
  rcases exists_ordered_simplificationTriple_and_scaledMinor hA hij hjk hi hj hk
      hijClass hjkClass with
    ⟨p, q, r, hpq, hqr, rfl, rfl, rfl, a, b, c, ha, hb, hc, hscale⟩
  rw [hscale, mul_eq_zero]
  simp only [mul_ne_zero (mul_ne_zero ha.ne' hb.ne') hc.ne', false_or]
  exact orderedMinor_simplified_eq_zero_iff_existsUnique_maximalInterval hA hSlopes hpq hqr

/-- Full row rank is preserved by canonical simplification under `TN₂`. -/
theorem hasFullRowRank_iff_simplifiedMatrix (hA : TNUpTo A 2) :
    HasFullRowRank A ↔ HasFullRowRank (simplifiedMatrix A) := by
  constructor
  · rintro ⟨cols, hcols⟩
    by_cases h0 : IsLoop A (cols 0)
    · exact (hcols (orderedMinor_allRows_eq_zero_of_isLoop A cols 0 h0)).elim
    by_cases h1 : IsLoop A (cols 1)
    · exact (hcols (orderedMinor_allRows_eq_zero_of_isLoop A cols 1 h1)).elim
    by_cases h2 : IsLoop A (cols 2)
    · exact (hcols (orderedMinor_allRows_eq_zero_of_isLoop A cols 2 h2)).elim
    have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
    have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
    let p := simplificationClassIndex A (cols 0) h0
    let q := simplificationClassIndex A (cols 1) h1
    let r := simplificationClassIndex A (cols 2) h2
    have hpq : p ≠ q := by
      intro hpq
      have hpar : ColumnsPositivelyParallel A (cols 0) (cols 1) :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel A h0 h1).mp hpq
      exact hcols (orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols
        (by decide) hpar)
    have hqr : q ≠ r := by
      intro hqr
      have hpar : ColumnsPositivelyParallel A (cols 1) (cols 2) :=
        (simplificationClassIndex_eq_iff_columnsPositivelyParallel A h1 h2).mp hqr
      exact hcols (orderedMinor_allRows_eq_zero_of_columnsPositivelyParallel A cols
        (by decide) hpar)
    rcases exists_ordered_simplificationTriple_and_scaledMinor hA h01 h12 h0 h1 h2 hpq hqr with
      ⟨p', q', r', hpq', hqr', _, _, _, a, b, c, ha, hb, hc, hscale⟩
    rw [selectedTripleEmbedding_eq cols] at hscale
    refine ⟨selectedTripleEmbedding p' q' r' hpq' hqr', ?_⟩
    intro hzero
    rw [hzero, mul_zero] at hscale
    exact hcols hscale
  · rintro ⟨cols, hcols⟩
    refine ⟨cols.trans (simplificationEmbedding A), ?_⟩
    have heq :
        orderedMinor A (allRows 3) (cols.trans (simplificationEmbedding A)) =
          orderedMinor (simplifiedMatrix A) (allRows 3) cols := by
      rw [orderedMinor_allRows_eq_threeColumnMatrix_det,
        orderedMinor_allRows_eq_threeColumnMatrix_det]
      rfl
    rw [heq]
    exact hcols

/-- The whole simplified vertex set is a single maximal nontrivial constant-slope run. -/
def WholeSimplifiedChainIsOneRun (A : Matrix (Fin 3) (Fin n) ℝ) : Prop :=
  ∃ I : MaximalConstantSlopeInterval A,
    I.start = 0 ∧ I.stop + 1 = simplificationSize A

/-- For a simplification with at least three vertices, being one whole run is equivalent to
constancy of all slopes from the first through the last vertex. -/
theorem wholeSimplifiedChainIsOneRun_iff_constantBetween
    (hsize : 3 ≤ simplificationSize A) :
    WholeSimplifiedChainIsOneRun A ↔
      SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A)
        0 (simplificationSize A - 1) := by
  constructor
  · rintro ⟨I, hstart, hstop⟩
    have hstopEq : I.stop = simplificationSize A - 1 := by omega
    intro t ht hlast
    have hIt : I.start ≤ t := by simpa only [hstart] using ht
    have htStop : t < I.stop := by simpa only [hstopEq] using hlast
    have hIc := I.constant (t := t) hIt htStop
    simpa only [hstart] using hIc
  · intro hconstant
    let I : MaximalConstantSlopeInterval A :=
      { start := 0
        stop := simplificationSize A - 1
        nontrivial := by omega
        stop_lt := by omega
        constant := hconstant
        maximal := by
          intro a b ha hb hbSize _
          constructor <;> omega }
    refine ⟨I, rfl, ?_⟩
    change (simplificationSize A - 1) + 1 = simplificationSize A
    omega

/-- When there are at least three simplified classes, the whole chain is one constant-slope
run exactly when the original three-row matrix has row rank at most two, expressed as failure
of `HasFullRowRank`. -/
theorem wholeSimplifiedChainIsOneRun_iff_not_hasFullRowRank
    (hA : TNUpTo A 2) (hSlopes : SimplifiedSlopesMonotone A)
    (hsize : 3 ≤ simplificationSize A) :
    WholeSimplifiedChainIsOneRun A ↔ ¬HasFullRowRank A := by
  rw [wholeSimplifiedChainIsOneRun_iff_constantBetween hsize]
  constructor
  · intro hconstant hfull
    have hfullSimplified := (hasFullRowRank_iff_simplifiedMatrix hA).mp hfull
    rcases hfullSimplified with ⟨cols, hcols⟩
    have h01 : cols 0 < cols 1 := cols.strictMono (by decide)
    have h12 : cols 1 < cols 2 := cols.strictMono (by decide)
    have hbetween :
        SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A)
          (cols 0).val (cols 2).val := by
      intro t h0t ht2
      have htWhole := hconstant (Nat.zero_le t) (by omega)
      have h0Whole := hconstant (Nat.zero_le (cols 0).val) (by omega)
      exact htWhole.trans h0Whole.symm
    have hzero :=
      (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hA hSlopes h01 h12).mpr
        hbetween
    rw [selectedTripleEmbedding_eq cols] at hzero
    exact hcols hzero
  · intro hnotFull
    have hnotSimplified : ¬HasFullRowRank (simplifiedMatrix A) := by
      intro hfull
      exact hnotFull ((hasFullRowRank_iff_simplifiedMatrix hA).mpr hfull)
    let p : Fin (simplificationSize A) := ⟨0, by omega⟩
    let q : Fin (simplificationSize A) := ⟨1, by omega⟩
    let r : Fin (simplificationSize A) := ⟨simplificationSize A - 1, by omega⟩
    have hpq : p < q := by
      change p.val < q.val
      dsimp [p, q]
      omega
    have hqr : q < r := by
      change q.val < r.val
      dsimp [q, r]
      omega
    have hzero :
        orderedMinor (simplifiedMatrix A) (allRows 3)
          (selectedTripleEmbedding p q r hpq hqr) = 0 := by
      by_contra hne
      exact hnotSimplified ⟨selectedTripleEmbedding p q r hpq hqr, hne⟩
    have hconstant :
        SlopesConstantBetween (simplifiedMomentU A) (simplifiedMomentV A) p.val r.val :=
      (orderedMinor_simplified_eq_zero_iff_slopesConstantBetween hA hSlopes hpq hqr).mp hzero
    intro t ht hlast
    exact hconstant (by simpa only [p] using ht) (by simpa only [r] using hlast)

end

end ToeplitzPositroids.RankThree
