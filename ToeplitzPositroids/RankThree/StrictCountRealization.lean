import ToeplitzPositroids.RankThree.OneSidedAssembly
import ToeplitzPositroids.RankThree.StrictCount
import Mathlib.Tactic

/-!
# Realization and exact counting in the strict rank-three Toeplitz region

This file completes the surjectivity part of Corollary 9.  A subset of the adjacent
comparisons is encoded by a positive weakly increasing slope family: the slope stays constant
at prescribed positions and rises by one at every other position.  Finite slope synthesis then
produces a positive Toeplitz matrix realizing exactly that pattern.

We also prove that the synthesized section lies in the strict order-two region.  Finally, the
finite family of actual maximal-minor zero supports is put in bijection with the non-universal
adjacent-equality patterns, giving the count `2^(n-2)-1`.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- The target slope family attached to an adjacent-equality pattern.  Every comparison not in
`P` contributes one permanent unit jump to all later slopes. -/
def strictPatternSlope {N : ℕ} (P : Finset (Fin (N - 1))) (j : Fin N) : ℝ :=
  1 + ∑ i ∈ Finset.range j.val, if i ∈ P.image Fin.val then (0 : ℝ) else 1

/-- The pattern slope family is everywhere positive. -/
theorem strictPatternSlope_pos {N : ℕ} (P : Finset (Fin (N - 1))) :
    ∀ j, 0 < strictPatternSlope P j := by
  intro j
  have hsum : 0 ≤ ∑ i ∈ Finset.range j.val,
      if i ∈ P.image Fin.val then (0 : ℝ) else 1 := by
    apply Finset.sum_nonneg
    intro i hi
    split <;> norm_num
  dsimp [strictPatternSlope]
  linarith

/-- The pattern slope family is weakly increasing. -/
theorem strictPatternSlope_monotone {N : ℕ} (P : Finset (Fin (N - 1))) :
    Monotone (strictPatternSlope P) := by
  intro i j hij
  have hval : i.val ≤ j.val := by simpa using hij
  have hsum :
      (∑ k ∈ Finset.range i.val,
          if k ∈ P.image Fin.val then (0 : ℝ) else 1) ≤
        ∑ k ∈ Finset.range j.val,
          if k ∈ P.image Fin.val then (0 : ℝ) else 1 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hval)
    intro k hk hki
    split <;> norm_num
  dsimp [strictPatternSlope]
  linarith

/-- The slope family is packaged with exactly the hypotheses required by finite synthesis. -/
theorem strictPatternSlope_isPositiveMonotone {N : ℕ} (P : Finset (Fin (N - 1))) :
    IsPositiveMonotoneSlopeFamily (strictPatternSlope P) :=
  ⟨strictPatternSlope_pos P, strictPatternSlope_monotone P⟩

/-- Two adjacent target slopes agree exactly at the prescribed comparison positions. -/
@[simp]
theorem strictPatternSlope_castSucc_eq_succ_iff {N : ℕ}
    (P : Finset (Fin (N - 1))) (t : Fin (N - 1)) :
    strictPatternSlope P ⟨t.val, by omega⟩ =
        strictPatternSlope P ⟨t.val + 1, by omega⟩ ↔
      t ∈ P := by
  simp only [strictPatternSlope, Finset.sum_range_succ]
  have himage : t.val ∈ P.image Fin.val ↔ t ∈ P := by
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨u, hu, huv⟩
      have hut : u = t := Fin.ext huv
      simpa [hut] using hu
    · intro ht
      exact ⟨t, ht, rfl⟩
  by_cases ht : t ∈ P
  · rw [if_pos (himage.mpr ht)]
    simp [ht]
  · rw [if_neg (fun h ↦ ht (himage.mp h))]
    simp [ht]

/-- Every admissible finite synthesis has positive entries and strictly positive ordered
two-by-two minors.  The three row-pair cases reduce respectively to strict increase of the
shifted ratios, of the products of two adjacent ratios, and of the unshifted ratios. -/
theorem synthesizedToeplitz_inStrictOrderTwoRegion {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    InStrictOrderTwoRegion
      (rankThreeToeplitz (synthesizedCoefficientVector s ε)) := by
  constructor
  · intro i j
    rw [rankThreeToeplitz_apply]
    exact synthesizedCoefficientVector_pos hε _
  · intro rows cols
    let i₀ := rows 0
    let i₁ := rows 1
    let p := cols 0
    let q := cols 1
    have hpq : p < q := cols.strictMono (by decide)
    have hrpq : finiteSynthesizedRatio s ε p.val < finiteSynthesizedRatio s ε q.val := by
      rw [finiteSynthesizedRatio_eq s ε (by omega),
        finiteSynthesizedRatio_eq s ε (by omega)]
      exact synthesizedRatio_strictMonoOn hε (by exact_mod_cast hpq) (by omega)
    have hrspq : finiteSynthesizedRatio s ε (p.val + 1) <
        finiteSynthesizedRatio s ε (q.val + 1) := by
      rw [finiteSynthesizedRatio_eq s ε (by omega),
        finiteSynthesizedRatio_eq s ε (by omega)]
      exact synthesizedRatio_strictMonoOn hε (by omega) (by omega)
    have hrp : 0 < finiteSynthesizedRatio s ε p.val :=
      finiteSynthesizedRatio_pos hε _
    have hrq : 0 < finiteSynthesizedRatio s ε q.val :=
      finiteSynthesizedRatio_pos hε _
    have hrps : 0 < finiteSynthesizedRatio s ε (p.val + 1) :=
      finiteSynthesizedRatio_pos hε _
    have hrqs : 0 < finiteSynthesizedRatio s ε (q.val + 1) :=
      finiteSynthesizedRatio_pos hε _
    have hcp : 0 < synthesizedCoefficientVector s ε p.succ.succ :=
      synthesizedCoefficientVector_pos hε _
    have hcq : 0 < synthesizedCoefficientVector s ε q.succ.succ :=
      synthesizedCoefficientVector_pos hε _
    have hpcol := synthesizedToeplitz_column hε p
    have hqcol := synthesizedToeplitz_column hε q
    have hp0 := congrFun hpcol i₀
    have hp1 := congrFun hpcol i₁
    have hq0 := congrFun hqcol i₀
    have hq1 := congrFun hqcol i₁
    change rankThreeToeplitz (synthesizedCoefficientVector s ε) i₀ p = _ at hp0
    change rankThreeToeplitz (synthesizedCoefficientVector s ε) i₁ p = _ at hp1
    change rankThreeToeplitz (synthesizedCoefficientVector s ε) i₀ q = _ at hq0
    change rankThreeToeplitz (synthesizedCoefficientVector s ε) i₁ q = _ at hq1
    rw [orderedMinor_two]
    change 0 <
      rankThreeToeplitz (synthesizedCoefficientVector s ε) i₀ p *
          rankThreeToeplitz (synthesizedCoefficientVector s ε) i₁ q -
        rankThreeToeplitz (synthesizedCoefficientVector s ε) i₀ q *
          rankThreeToeplitz (synthesizedCoefficientVector s ε) i₁ p
    rw [hp0, hp1, hq0, hq1]
    have hrows : i₀ < i₁ := rows.strictMono (by decide)
    have hpairsVal :
        (i₀.val = 0 ∧ i₁.val = 1) ∨ (i₀.val = 0 ∧ i₁.val = 2) ∨
          (i₀.val = 1 ∧ i₁.val = 2) := by
      omega
    have hpairs :
        (i₀ = 0 ∧ i₁ = 1) ∨ (i₀ = 0 ∧ i₁ = 2) ∨ (i₀ = 1 ∧ i₁ = 2) := by
      rcases hpairsVal with h01 | h02 | h12
      · exact Or.inl ⟨Fin.ext h01.1, Fin.ext h01.2⟩
      · exact Or.inr (Or.inl ⟨Fin.ext h02.1, Fin.ext h02.2⟩)
      · exact Or.inr (Or.inr ⟨Fin.ext h12.1, Fin.ext h12.2⟩)
    rcases hpairs with h01 | h02 | h12
    · rcases h01 with ⟨h0, h1⟩
      simp [h0, h1, ratioPointX, ratioPointY]
      nlinarith [mul_pos (mul_pos hcp hcq) (sub_pos.mpr hrspq)]
    · rcases h02 with ⟨h0, h2⟩
      have hprod :
          finiteSynthesizedRatio s ε p.val * finiteSynthesizedRatio s ε (p.val + 1) <
            finiteSynthesizedRatio s ε q.val *
              finiteSynthesizedRatio s ε (q.val + 1) := by
        nlinarith
      simp [h0, h2, ratioPointX, ratioPointY]
      nlinarith [mul_pos (mul_pos hcp hcq) (sub_pos.mpr hprod)]
    · rcases h12 with ⟨h1, h2⟩
      simp [h1, h2, ratioPointX, ratioPointY]
      nlinarith [mul_pos (mul_pos (mul_pos (mul_pos hcp hcq) hrps) hrqs)
        (sub_pos.mpr hrpq)]

/-- A synthesized consecutive maximal minor vanishes exactly at a prescribed equality. -/
theorem synthesizedToeplitz_consecutiveMinor_eq_zero_iff {N : ℕ}
    (P : Finset (Fin (N - 1))) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon (strictPatternSlope P) ε)
    (t : Fin (N - 1)) :
    orderedMinor
        (rankThreeToeplitz (synthesizedCoefficientVector (strictPatternSlope P) ε))
        (allRows 3) (strictConsecutiveTripleEmbedding t) = 0 ↔
      t ∈ P := by
  let i : Fin (N + 1) := ⟨t.val, by omega⟩
  let j : Fin (N + 1) := ⟨t.val + 1, by omega⟩
  let k : Fin (N + 1) := ⟨t.val + 2, by omega⟩
  have hij : i < j := by simp [i, j]
  have hjk : j < k := by simp [j, k]
  have hembed : strictConsecutiveTripleEmbedding t =
      selectedTripleEmbedding i j k hij hjk := by
    apply RelEmbedding.ext
    intro u
    fin_cases u <;> rfl
  rw [hembed, synthesizedToeplitz_minor_eq_area hε hij hjk]
  have hscale :
      synthesizedCoefficientVector (strictPatternSlope P) ε i.succ.succ *
          synthesizedCoefficientVector (strictPatternSlope P) ε j.succ.succ *
          synthesizedCoefficientVector (strictPatternSlope P) ε k.succ.succ ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (synthesizedCoefficientVector_pos hε _).ne'
        (synthesizedCoefficientVector_pos hε _).ne')
      (synthesizedCoefficientVector_pos hε _).ne'
  rw [mul_eq_zero]
  simp only [hscale, false_or]
  change orientedArea
      (ratioPointX (finiteSynthesizedRatio (strictPatternSlope P) ε))
      (ratioPointY (finiteSynthesizedRatio (strictPatternSlope P) ε))
      t.val (t.val + 1) (t.val + 2) = 0 ↔ _
  rw [orientedArea_consecutive_eq_zero_iff _ _
    (finiteSynthesizedRatio_pointX_strict hε (by omega) (by omega))
    (finiteSynthesizedRatio_pointX_strict hε (by omega) (by omega)),
    finiteSynthesizedRatio_edgeSlope hε ⟨t.val, by omega⟩,
    finiteSynthesizedRatio_edgeSlope hε ⟨t.val + 1, by omega⟩]
  exact strictPatternSlope_castSucc_eq_succ_iff P t

/-- The Pascal-moment slope-equality pattern of the synthesized matrix is exactly `P`. -/
theorem synthesizedToeplitz_slopeEqualityPattern {N : ℕ}
    (P : Finset (Fin (N - 1))) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon (strictPatternSlope P) ε) :
    slopeEqualityPattern
        (rankThreeToeplitz (synthesizedCoefficientVector (strictPatternSlope P) ε)) =
      P := by
  let A := rankThreeToeplitz (synthesizedCoefficientVector (strictPatternSlope P) ε)
  have hstrict : InStrictOrderTwoRegion A := synthesizedToeplitz_inStrictOrderTwoRegion hε
  calc
    slopeEqualityPattern A = consecutiveMinorZeroPattern A :=
      (consecutiveMinorZeroPattern_eq_slopeEqualityPattern hstrict.tnUpTo_two
        hstrict.isSimpleNonloopConfiguration).symm
    _ = P := by
      ext t
      rw [mem_consecutiveMinorZeroPattern_iff]
      exact synthesizedToeplitz_consecutiveMinor_eq_zero_iff P hε t

/-- The consecutive-maximal-minor zero pattern of the synthesized matrix is exactly `P`. -/
theorem synthesizedToeplitz_consecutiveMinorZeroPattern {N : ℕ}
    (P : Finset (Fin (N - 1))) {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon (strictPatternSlope P) ε) :
    consecutiveMinorZeroPattern
        (rankThreeToeplitz (synthesizedCoefficientVector (strictPatternSlope P) ε)) =
      P := by
  ext t
  rw [mem_consecutiveMinorZeroPattern_iff]
  exact synthesizedToeplitz_consecutiveMinor_eq_zero_iff P hε t

/-- A packaged positive, strict-order-two, totally nonnegative, full-row-rank Toeplitz
realization. -/
structure StrictToeplitzRealization (n : ℕ) where
  coefficients : Fin (n + 2) → ℝ
  coefficients_pos : ∀ k, 0 < coefficients k
  strictOrderTwo : InStrictToeplitzRegion coefficients
  totallyNonnegative : TotallyNonnegative (rankThreeToeplitz coefficients)
  fullRowRank : HasFullRowRank (rankThreeToeplitz coefficients)

namespace StrictToeplitzRealization

/-- The adjacent moment-slope equality pattern of a packaged realization. -/
def equalityPattern {n : ℕ} (R : StrictToeplitzRealization n) :
    Finset (Fin (n - 2)) :=
  slopeEqualityPattern (rankThreeToeplitz R.coefficients)

/-- The consecutive-maximal-minor zero pattern of a packaged realization. -/
def consecutiveZeroPattern {n : ℕ} (R : StrictToeplitzRealization n) :
    Finset (Fin (n - 2)) :=
  consecutiveMinorZeroPattern (rankThreeToeplitz R.coefficients)

end StrictToeplitzRealization

/-- Every non-universal pattern for `N+1` columns is realized by finite slope synthesis. -/
theorem exists_strictToeplitzRealization_succ {N : ℕ} (hN : 2 ≤ N)
    (P : Finset (Fin (N - 1))) (hP : P ≠ Finset.univ) :
    ∃ R : StrictToeplitzRealization (N + 1),
      R.equalityPattern = P ∧ R.consecutiveZeroPattern = P := by
  classical
  have hs := strictPatternSlope_isPositiveMonotone P
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  have hex : ∃ t : Fin (N - 1), t ∉ P := by
    by_contra hnone
    apply hP
    apply Finset.eq_univ_iff_forall.mpr
    intro t
    by_contra ht
    exact hnone ⟨t, ht⟩
  obtain ⟨t, ht⟩ := hex
  have hle :
      strictPatternSlope P ⟨t.val, by omega⟩ ≤
        strictPatternSlope P ⟨t.val + 1, by omega⟩ :=
    strictPatternSlope_monotone P (by simp)
  have hne :
      strictPatternSlope P ⟨t.val, by omega⟩ ≠
        strictPatternSlope P ⟨t.val + 1, by omega⟩ :=
    (strictPatternSlope_castSucc_eq_succ_iff P t).not.mpr ht
  have hstrictSlope :
      strictPatternSlope P ⟨t.val, by omega⟩ <
        strictPatternSlope P ⟨t.val + 1, by omega⟩ :=
    lt_of_le_of_ne hle hne
  let R : StrictToeplitzRealization (N + 1) :=
    { coefficients := synthesizedCoefficientVector (strictPatternSlope P) ε
      coefficients_pos := synthesizedCoefficientVector_pos hε
      strictOrderTwo := synthesizedToeplitz_inStrictOrderTwoRegion hε
      totallyNonnegative :=
        synthesizedToeplitz_totallyNonnegative hN hε (strictPatternSlope_monotone P)
      fullRowRank :=
        synthesizedToeplitz_hasFullRowRank_of_strictSlope hε (by omega) hstrictSlope }
  refine ⟨R, ?_, ?_⟩
  · exact synthesizedToeplitz_slopeEqualityPattern P hε
  · exact synthesizedToeplitz_consecutiveMinorZeroPattern P hε

/-- Every non-universal subset of the `n-2` adjacent comparisons is realized by a positive
rank-three Toeplitz matrix in the strict order-two region. -/
theorem exists_strictToeplitzRealization {n : ℕ} (hn : 3 ≤ n)
    (P : Finset (Fin (n - 2))) (hP : P ≠ Finset.univ) :
    ∃ R : StrictToeplitzRealization n,
      R.equalityPattern = P ∧ R.consecutiveZeroPattern = P := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, n = d + 3 := ⟨n - 3, by omega⟩
  simpa using exists_strictToeplitzRealization_succ (N := d + 2) (by omega) P hP

/-- Coefficient-level form of strict-pattern surjectivity. -/
theorem exists_positiveToeplitz_with_pattern {n : ℕ} (hn : 3 ≤ n)
    (P : Finset (Fin (n - 2))) (hP : P ≠ Finset.univ) :
    ∃ a : Fin (n + 2) → ℝ,
      (∀ k, 0 < a k) ∧ InStrictToeplitzRegion a ∧
        TotallyNonnegative (rankThreeToeplitz a) ∧
        HasFullRowRank (rankThreeToeplitz a) ∧
        slopeEqualityPattern (rankThreeToeplitz a) = P ∧
        consecutiveMinorZeroPattern (rankThreeToeplitz a) = P := by
  obtain ⟨R, heq, hzero⟩ := exists_strictToeplitzRealization hn P hP
  exact ⟨R.coefficients, R.coefficients_pos, R.strictOrderTwo,
    R.totallyNonnegative, R.fullRowRank, heq, hzero⟩

/-- The finite set of ordered maximal minors that vanish for a three-row matrix. -/
noncomputable def maximalMinorZeroPattern {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) : Finset (Fin 3 ↪o Fin n) := by
  classical
  exact Finset.univ.filter fun cols ↦ orderedMinor A (allRows 3) cols = 0

@[simp]
theorem mem_maximalMinorZeroPattern_iff {n : ℕ}
    (A : Matrix (Fin 3) (Fin n) ℝ) (cols : Fin 3 ↪o Fin n) :
    cols ∈ maximalMinorZeroPattern A ↔ orderedMinor A (allRows 3) cols = 0 := by
  classical
  simp [maximalMinorZeroPattern]

namespace StrictToeplitzRealization

/-- The complete ordered maximal-minor zero support of a packaged realization. -/
noncomputable def maximalZeroSupport {n : ℕ} (R : StrictToeplitzRealization n) :
    Finset (Fin 3 ↪o Fin n) :=
  maximalMinorZeroPattern (rankThreeToeplitz R.coefficients)

/-- In the strict totally nonnegative region, the adjacent equality code and the complete
maximal-minor zero support determine one another. -/
theorem equalityPattern_eq_iff_maximalZeroSupport_eq {n : ℕ}
    (R S : StrictToeplitzRealization n) :
    R.equalityPattern = S.equalityPattern ↔ R.maximalZeroSupport = S.maximalZeroSupport := by
  have hclassification := strictRegion_slopeEqualityPattern_eq_iff_maximalMinorZeroSupport_eq
    R.strictOrderTwo S.strictOrderTwo R.totallyNonnegative S.totallyNonnegative
  constructor
  · intro hpattern
    ext cols
    simp only [maximalZeroSupport, mem_maximalMinorZeroPattern_iff]
    exact hclassification.mp hpattern cols
  · intro hsupport
    apply hclassification.mpr
    intro cols
    have hmem := Finset.ext_iff.mp hsupport cols
    simpa only [maximalZeroSupport, mem_maximalMinorZeroPattern_iff] using hmem

end StrictToeplitzRealization

/-- The finite family of complete maximal-minor zero supports realized in the positive strict
Toeplitz region with full row rank. -/
noncomputable def realizedStrictToeplitzSupports (n : ℕ) :
    Finset (Finset (Fin 3 ↪o Fin n)) := by
  classical
  exact Finset.univ.filter fun S ↦
    ∃ R : StrictToeplitzRealization n, R.maximalZeroSupport = S

@[simp]
theorem mem_realizedStrictToeplitzSupports_iff {n : ℕ}
    (S : Finset (Fin 3 ↪o Fin n)) :
    S ∈ realizedStrictToeplitzSupports n ↔
      ∃ R : StrictToeplitzRealization n, R.maximalZeroSupport = S := by
  classical
  simp [realizedStrictToeplitzSupports]

/-- Choose a realization of a support known to belong to the realized support family. -/
noncomputable def realizationOfRealizedSupport {n : ℕ}
    (S : Finset (Fin 3 ↪o Fin n)) (hS : S ∈ realizedStrictToeplitzSupports n) :
    StrictToeplitzRealization n :=
  Classical.choose ((mem_realizedStrictToeplitzSupports_iff S).mp hS)

/-- The chosen realization has the support from which it was selected. -/
theorem realizationOfRealizedSupport_maximalZeroSupport {n : ℕ}
    (S : Finset (Fin 3 ↪o Fin n)) (hS : S ∈ realizedStrictToeplitzSupports n) :
    (realizationOfRealizedSupport S hS).maximalZeroSupport = S :=
  Classical.choose_spec ((mem_realizedStrictToeplitzSupports_iff S).mp hS)

/-- The realized complete zero supports are in bijection with the non-universal adjacent
equality patterns. -/
theorem card_realizedStrictToeplitzSupports_eq_fullRankEqualityPatterns {n : ℕ}
    (hn : 3 ≤ n) :
    (realizedStrictToeplitzSupports n).card = (fullRankEqualityPatterns n).card := by
  classical
  let encode : (S : Finset (Fin 3 ↪o Fin n)) →
      S ∈ realizedStrictToeplitzSupports n → Finset (Fin (n - 2)) :=
    fun S hS ↦ (realizationOfRealizedSupport S hS).equalityPattern
  apply Finset.card_bij encode
  · intro S hS
    let R := realizationOfRealizedSupport S hS
    exact slopeEqualityPattern_mem_fullRankEqualityPatterns R.strictOrderTwo
      R.totallyNonnegative R.fullRowRank
  · intro S hS T hT hcode
    let R := realizationOfRealizedSupport S hS
    let Q := realizationOfRealizedSupport T hT
    have hsupport : R.maximalZeroSupport = Q.maximalZeroSupport :=
      (R.equalityPattern_eq_iff_maximalZeroSupport_eq Q).mp hcode
    calc
      S = R.maximalZeroSupport :=
        (realizationOfRealizedSupport_maximalZeroSupport S hS).symm
      _ = Q.maximalZeroSupport := hsupport
      _ = T := realizationOfRealizedSupport_maximalZeroSupport T hT
  · intro P hP
    have hPne : P ≠ Finset.univ := by
      have := (mem_fullRankEqualityPatterns_iff.mp hP)
      simpa [allEqualPattern] using this
    obtain ⟨R, hReq, hRzero⟩ := exists_strictToeplitzRealization hn P hPne
    let S := R.maximalZeroSupport
    have hS : S ∈ realizedStrictToeplitzSupports n :=
      (mem_realizedStrictToeplitzSupports_iff S).mpr ⟨R, rfl⟩
    refine ⟨S, hS, ?_⟩
    change (realizationOfRealizedSupport S hS).equalityPattern = P
    calc
      (realizationOfRealizedSupport S hS).equalityPattern = R.equalityPattern :=
        ((realizationOfRealizedSupport S hS).equalityPattern_eq_iff_maximalZeroSupport_eq R).mpr
          (by
            simpa [S] using realizationOfRealizedSupport_maximalZeroSupport S hS)
      _ = P := hReq

/-- Corollary 9: the exact number of complete maximal-minor zero supports in the positive
strict-order-two, totally nonnegative, full-row-rank rank-three Toeplitz region is
`2^(n-2)-1`. -/
theorem card_realizedStrictToeplitzSupports {n : ℕ} (hn : 3 ≤ n) :
    (realizedStrictToeplitzSupports n).card = 2 ^ (n - 2) - 1 := by
  rw [card_realizedStrictToeplitzSupports_eq_fullRankEqualityPatterns hn]
  exact card_fullRankEqualityPatterns

end

end ToeplitzPositroids.RankThree
