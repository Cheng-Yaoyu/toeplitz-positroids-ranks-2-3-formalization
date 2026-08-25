import ToeplitzPositroids.RankThree.SinePerturbation
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Arbitrary interior zero patterns

This file assembles the inverse-function-theorem argument of Theorem 20.  The
local-surjectivity lemma is stated abstractly for any supplied invertible strict
derivative.  The sine specialization then feeds the shrinking target vectors
from `SinePerturbation` into that local inverse.
-/

namespace ToeplitzPositroids.RankThree

open Filter Set Topology
open ToeplitzPositroids

noncomputable section

variable {d : ℕ}

section AbstractIFT

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A reusable local-surjectivity wrapper around mathlib's inverse function
theorem.  Any target sequence converging to `f a` is eventually realized by
points in every prescribed source neighborhood of `a`. -/
theorem exists_local_preimage_of_tendsto
    {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f'.toContinuousLinearMap a)
    {U : Set E} (hU : U ∈ 𝓝 a) {y : ℕ → F}
    (hy : Tendsto y atTop (𝓝 (f a))) :
    ∃ N : ℕ, ∃ x ∈ U, f x = y N := by
  let g : F → E := hf.localInverse f f' a
  have hsource : ∀ᶠ z in 𝓝 (f a), g z ∈ U := hf.localInverse_tendsto.eventually hU
  have hright : ∀ᶠ z in 𝓝 (f a), f (g z) = z := hf.eventually_right_inverse
  obtain ⟨N, hNU, hNR⟩ := (hy.eventually (hsource.and hright)).exists
  exact ⟨N, g (y N), hNU, hNR⟩

/-- The same local-surjectivity statement while retaining an arbitrary property
of every member of the target sequence. -/
theorem exists_local_preimage_with_target_property
    {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f'.toContinuousLinearMap a)
    {U : Set E} (hU : U ∈ 𝓝 a) {y : ℕ → F}
    (hy : Tendsto y atTop (𝓝 (f a))) {P : F → Prop}
    (hP : ∀ N, P (y N)) :
    ∃ N : ℕ, ∃ x ∈ U, f x = y N ∧ P (f x) := by
  obtain ⟨N, x, hx, hfx⟩ := exists_local_preimage_of_tendsto hf hU hy
  exact ⟨N, x, hx, hfx, hfx.symm ▸ hP N⟩

end AbstractIFT

/-- The fixed-endpoint determinant map vanishes at the sine interior point. -/
theorem consecutiveInteriorMap_sineInterior_eq_zero (hd : 2 ≤ d) :
    consecutiveInteriorMap d (sineInterior d) = 0 := by
  funext i
  rw [consecutiveInteriorMap_apply_eq_consecutiveDeterminant hd,
    fixedEndpointBand_sineInterior]
  have hi := i.isLt
  let t : Fin (d + 1) := ⟨i.val + 1, by omega⟩
  exact sineConsecutiveDeterminant_eq_zero hd t (by simp [t]) (by simp [t]; omega)

/-- Reinserting the fixed endpoints does not increase the sup norm of an
interior perturbation. -/
theorem fixedEndpointBand_norm_sub_sine_le (d : ℕ) (x : Fin (d - 1) → ℝ) :
    ‖fixedEndpointBand d x - sineCoefficient d‖ ≤ ‖x - sineInterior d‖ := by
  rw [← fixedEndpointBand_sineInterior]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro t
  simp only [Pi.sub_apply, fixedEndpointBand]
  unfold fixedEndpointCoefficient
  split_ifs with ht
  · exact norm_le_pi_norm (x - sineInterior d) ⟨((t : ℤ) - 1).toNat, by omega⟩
  · simp

/-- Strict zero-boundary log-concavity forces strict decrease of adjacent
coefficient ratios on every positive three-term window. -/
theorem strictBandCoefficientRatio_succ_lt
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (k : Fin (d + 3))
    (hleft : 0 < bandCoefficientVector b k.castSucc.castSucc)
    (hcenter : 0 < bandCoefficientVector b k.succ.castSucc) :
    coefficientRatio (bandCoefficientVector b) k.succ <
      coefficientRatio (bandCoefficientVector b) k.castSucc := by
  have hcenterBand : 0 < bandCoefficient b ((k : ℤ) - 1) := by
    simpa only [bandCoefficientVector_center] using hcenter
  have hk := (bandCoefficient_pos_iff hb.1 ((k : ℤ) - 1)).mp hcenterBand
  let t : Fin (d + 1) := ⟨((k : ℤ) - 1).toNat, by omega⟩
  have ht : (t : ℤ) = (k : ℤ) - 1 := by
    simp only [t]
    rw [Int.toNat_of_nonneg hk.1]
  have hstrict := hb.2 t
  have hcenterEq : b t = bandCoefficient b ((k : ℤ) - 1) := by
    rw [← bandCoefficient_apply_fin b t, ht]
  have hleftEq : bandCoefficient b ((t : ℤ) - 1) =
      bandCoefficient b ((k : ℤ) - 2) := by congr 1; omega
  have hrightEq : bandCoefficient b ((t : ℤ) + 1) = bandCoefficient b k := by
    congr 1
    omega
  rw [hleftEq, hrightEq, hcenterEq] at hstrict
  rw [coefficientRatio_apply, coefficientRatio_apply]
  have hmiddle : k.castSucc.succ = k.succ.castSucc := by apply Fin.ext; rfl
  rw [hmiddle, bandCoefficientVector_right, bandCoefficientVector_center,
    bandCoefficientVector_left]
  apply (div_lt_div_iff₀ (by simpa only [bandCoefficientVector_center] using hcenter)
    (by simpa only [bandCoefficientVector_left] using hleft)).2
  nlinarith

/-- Every nonstructural order-two minor is strictly positive for an arbitrary
positive strictly zero-boundary-log-concave band. -/
theorem bandedMatrix_nonstructural_twoMinor_pos
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ j₁ : Fin (d + 3)) (hj : j₀ < j₁)
    (hminor : IsNonstructuralTwoMinor (bandCoefficientVector b) i₀ i₁ j₀ j₁) :
    0 < orderedMinor (bandedMatrix b) (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj) := by
  let a := bandCoefficientVector b
  have hnonnegCoeff : ∀ k, 0 ≤ a k := bandCoefficientVector_nonneg hb.1
  have hsupport : HasIntervalPositiveSupport a :=
    bandCoefficientVector_hasIntervalPositiveSupport hb.1
  have hlog : DiscretelyLogConcave a := bandCoefficientVector_discretelyLogConcave hb
  have hC : TNUpTo (bandedMatrix b) 2 := bandedMatrix_tnUpTo_two_of_strictLogConcave hb
  have hnonneg := hC.orderedMinor_nonneg le_rfl
    (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj)
  by_contra hnot
  have hzero : orderedMinor (bandedMatrix b) (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj) = 0 :=
    le_antisymm (not_lt.mp hnot) hnonneg
  have hzero' : orderedMinor (rankThreeToeplitz a) (twoPointOrderEmbedding i₀ i₁ hi)
      (twoPointOrderEmbedding j₀ j₁ hj) = 0 := by
    simpa [a, bandedMatrix_eq_rankThreeToeplitz] using hzero
  have hconst := (rankThreeToeplitz_nonstructural_minor_eq_zero_iff_ratio_const
    hnonnegCoeff hsupport hlog i₀ i₁ hi j₀ j₁ hj hminor).mp hzero'
  let s := minorRatioStart i₀ i₁ hi j₀
  let e := finiteToeplitzIndex i₀ j₁
  have hgap : s.val + 2 ≤ e.val := by
    simp only [s, e, minorRatioStart_val, finiteToeplitzIndex_val]
    omega
  let k : Fin (d + 3) := ⟨s.val, by omega⟩
  have hs : s = k.castSucc := by apply Fin.ext; rfl
  have hlowerIndex : finiteToeplitzIndex i₁ j₀ = k.castSucc.castSucc := by
    apply Fin.ext
    rfl
  have hleft : 0 < a k.castSucc.castSucc := by
    rw [← hlowerIndex]
    exact hminor.2.2.1
  have hcenter : 0 < a k.succ.castSucc := by
    apply (hasIntervalPositiveSupport_iff a).mp hsupport
      (finiteToeplitzIndex i₁ j₀) (finiteToeplitzIndex i₀ j₁)
        k.succ.castSucc hminor.2.2.1 hminor.2.1
    · change (finiteToeplitzIndex i₁ j₀).val ≤ k.val + 1
      simp only [k, s, minorRatioStart_val]
      omega
    · change k.val + 1 ≤ (finiteToeplitzIndex i₀ j₁).val
      simp only [k]
      omega
  have hratioStrict := strictBandCoefficientRatio_succ_lt hb k hleft hcenter
  have hratioEq : coefficientRatio a k.succ = coefficientRatio a s := hconst k.succ (by
    change s.val ≤ k.val + 1
    simp [k]) (by
    change k.val + 1 < e.val
    simp only [k]
    omega)
  rw [hs] at hratioEq
  exact (ne_of_lt hratioStrict) hratioEq

/-- Strict zero-boundary log-concavity makes the banded column configuration
loop-free and simple. -/
theorem bandedMatrix_isSimpleNonloopConfiguration
    {b : Fin (d + 1) → ℝ} (hd : 2 ≤ d)
    (hb : StrictlyLogConcaveWithZeroBoundary b) :
    IsSimpleNonloopConfiguration (bandedMatrix b) := by
  let C := bandedMatrix b
  have hC := bandedMatrix_tnUpTo_two_of_strictLogConcave hb
  have hentry : ∀ (i : Fin 3) (j : Fin (d + 3)), 0 < C i j ↔
      (0 : ℤ) ≤ (j : ℤ) - i ∧ (j : ℤ) - i ≤ d := by
    intro i j
    exact bandCoefficient_pos_iff hb.1 _
  constructor
  · intro j hloop
    rw [isLoop_iff_entry_eq_zero] at hloop
    by_cases hj : j.val ≤ d
    · have hpos : 0 < C 0 j := (hentry 0 j).2 (by omega)
      exact hpos.ne' (hloop 0)
    · have hpos : 0 < C 2 j := (hentry 2 j).2 (by omega)
      exact hpos.ne' (hloop 2)
  · intro i j hij hparallel
    obtain ⟨c, hc, hcol⟩ := hparallel
    have hposiff : ∀ r : Fin 3, 0 < C r i ↔ 0 < C r j := by
      intro r
      have hcoord := congrFun hcol r
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hcoord
      constructor
      · intro hi
        change 0 < bandedMatrix b r i at hi
        change 0 < bandedMatrix b r j
        rw [hcoord]
        exact mul_pos hc hi
      · intro hj
        change 0 < bandedMatrix b r j at hj
        change 0 < bandedMatrix b r i
        have hinonneg := hC.entry_nonneg (by omega) r i
        rw [hcoord] at hj
        nlinarith
    have h₀ := hposiff 0
    have h₁ := hposiff 1
    have h₂ := hposiff 2
    simp only [hentry] at h₀ h₁ h₂
    have hinterior : 2 ≤ i.val ∧ j.val ≤ d := by omega
    have hminor : IsNonstructuralTwoMinor (bandCoefficientVector b) (0 : Fin 3) 1 i j := by
      have h00 : 0 < C 0 i := (hentry 0 i).2 (by omega)
      have h01 : 0 < C 0 j := (hentry 0 j).2 (by omega)
      have h10 : 0 < C 1 i := (hentry 1 i).2 (by omega)
      have h11 : 0 < C 1 j := (hentry 1 j).2 (by omega)
      dsimp only [C] at h00 h01 h10 h11
      rw [bandedMatrix_eq_rankThreeToeplitz] at h00 h01 h10 h11
      exact ⟨h00, h01, h10, h11⟩
    have hposminor := bandedMatrix_nonstructural_twoMinor_pos hb
      (0 : Fin 3) 1 (by decide) i j hij hminor
    have hzero : orderedMinor C (twoPointOrderEmbedding (0 : Fin 3) 1 (by decide))
        (twoPointOrderEmbedding i j hij) = 0 := by
      rw [orderedMinor_two]
      simp only [twoPointOrderEmbedding_zero, twoPointOrderEmbedding_one]
      dsimp only [C]
      have hc₀ := congrFun hcol (0 : Fin 3)
      have hc₁ := congrFun hcol (1 : Fin 3)
      simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul] at hc₀ hc₁
      rw [hc₀, hc₁]
      ring
    exact hposminor.ne' hzero

/-- Nonnegative consecutive determinants make every moment slope comparison
weakly increasing, hence make the whole banded matrix totally nonnegative. -/
theorem bandedMatrix_totallyNonnegative_of_consecutive_nonneg
    {b : Fin (d + 1) → ℝ} (hb : StrictlyLogConcaveWithZeroBoundary b)
    (hsimple : IsSimpleNonloopConfiguration (bandedMatrix b))
    (hdet : ∀ t, 0 ≤ consecutiveDeterminant b t) :
    TotallyNonnegative (bandedMatrix b) := by
  have hTwo := bandedMatrix_tnUpTo_two_of_strictLogConcave hb
  apply (totallyNonnegative_iff_momentSlopesMonotone hTwo hsimple).mpr
  apply (slopesMonotoneUpTo_iff_consecutive _ _
    (matrixMomentU_strictlyIncreasingUpTo hTwo hsimple)).mpr
  intro i hi
  let t : Fin (d + 1) := ⟨i, by omega⟩
  have hslope := (consecutiveDeterminant_nonneg_iff_slope_le hb hsimple t).mp (hdet t)
  rw [bandMomentSlope_eq_edgeSlope, bandMomentSlope_eq_edgeSlope] at hslope
  simpa [t, consecutiveSlopeIndex] using hslope

/-- The positive left endpoint determinant witnesses full row rank for every
positive band. -/
theorem bandedMatrix_hasFullRowRank_of_positive
    {b : Fin (d + 1) → ℝ} (hb : PositiveBandCoefficients b) :
    HasFullRowRank (bandedMatrix b) := by
  let i : Fin (d + 3) := ⟨0, by omega⟩
  let j : Fin (d + 3) := ⟨1, by omega⟩
  let k : Fin (d + 3) := ⟨2, by omega⟩
  have hij : i < j := by simp [i, j]
  have hjk : j < k := by change (1 : ℕ) < 2; omega
  refine ⟨selectedTripleEmbedding i j k hij hjk, ?_⟩
  rw [orderedMinor_selectedTriple_eq_threeColumnMatrix_det]
  change consecutiveDeterminant b 0 ≠ 0
  rw [consecutiveDeterminant_zero]
  exact (pow_pos (hb 0) 3).ne'

/-- Theorem 20 with the inverse derivative supplied explicitly.  This theorem
is the complete geometric and matrix-theoretic assembly; the final paper
theorem instantiates `f'` with the unconditional sine Jacobian equivalence. -/
theorem arbitraryZeroPattern_of_equiv
    (hd : 2 ≤ d)
    (f' : (Fin (d - 1) → ℝ) ≃L[ℝ] (Fin (d - 1) → ℝ))
    (hf : HasStrictFDerivAt (consecutiveInteriorMap d)
      f'.toContinuousLinearMap (sineInterior d))
    (Z : Set (Fin (d - 1))) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ b : Fin (d + 1) → ℝ,
      StrictlyLogConcaveWithZeroBoundary b ∧
      ‖b - sineCoefficient d‖ < epsilon ∧
      (∀ i : Fin (d - 1),
        consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔ i ∈ Z) ∧
      TNUpTo (bandedMatrix b) 2 ∧
      TotallyNonnegative (bandedMatrix b) ∧
      HasFullRowRank (bandedMatrix b) ∧
      ∀ (i₀ i₁ : Fin 3) (hi : i₀ < i₁)
        (j₀ j₁ : Fin (d + 3)) (hj : j₀ < j₁),
        IsNonstructuralTwoMinor (bandCoefficientVector b) i₀ i₁ j₀ j₁ →
          0 < orderedMinor (bandedMatrix b)
            (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj) := by
  have hmapZero := consecutiveInteriorMap_sineInterior_eq_zero hd
  have htargets : Tendsto (shrinkingTarget Z) atTop
      (𝓝 (consecutiveInteriorMap d (sineInterior d))) := by
    rw [hmapZero]
    exact shrinkingTarget_tendsto_zero Z
  have hsource : sineSourceNeighborhood d epsilon ∈ 𝓝 (sineInterior d) :=
    sineSourceNeighborhood_mem_nhds hd hepsilon
  obtain ⟨N, x, hx, hmap⟩ :=
    exists_local_preimage_of_tendsto hf hsource htargets
  let b : Fin (d + 1) → ℝ := fixedEndpointBand d x
  have hb : StrictlyLogConcaveWithZeroBoundary b := by
    exact sourceNeighborhood_admissible hx
  have hcloseInterior : ‖x - sineInterior d‖ < epsilon :=
    sourceNeighborhood_norm_sub_lt hx
  have hclose : ‖b - sineCoefficient d‖ < epsilon :=
    (fixedEndpointBand_norm_sub_sine_le d x).trans_lt hcloseInterior
  have hpattern : ∀ i : Fin (d - 1),
      consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔ i ∈ Z := by
    intro i
    rw [← consecutiveInteriorMap_apply_eq_consecutiveDeterminant hd]
    rw [hmap]
    exact shrinkingTarget_eq_zero_iff N i
  have hTwo : TNUpTo (bandedMatrix b) 2 :=
    bandedMatrix_tnUpTo_two_of_strictLogConcave hb
  have hsimple : IsSimpleNonloopConfiguration (bandedMatrix b) :=
    bandedMatrix_isSimpleNonloopConfiguration hd hb
  have hdetNonneg : ∀ t : Fin (d + 1), 0 ≤ consecutiveDeterminant b t := by
    intro t
    by_cases ht0 : t.val = 0
    · have ht : t = 0 := Fin.ext ht0
      subst t
      rw [consecutiveDeterminant_zero]
      exact (pow_pos (hb.1 0) 3).le
    by_cases htd : t.val = d
    · have ht : t = Fin.last d := Fin.ext htd
      subst t
      rw [consecutiveDeterminant_last]
      exact (pow_pos (hb.1 (Fin.last d)) 3).le
    · let i : Fin (d - 1) := ⟨t.val - 1, by omega⟩
      have ht : (⟨i + 1, by omega⟩ : Fin (d + 1)) = t := by
        apply Fin.ext
        simp [i]
        omega
      have hcoord := congrFun hmap i
      rw [consecutiveInteriorMap_apply_eq_consecutiveDeterminant hd] at hcoord
      have hnonneg : 0 ≤ shrinkingTarget Z N i := by
        exact targetIndicator_pos_smul_nonneg (shrinkingTarget_scale_pos N) i
      rw [← hcoord, ht] at hnonneg
      exact hnonneg
  have hTNN : TotallyNonnegative (bandedMatrix b) :=
    bandedMatrix_totallyNonnegative_of_consecutive_nonneg hb hsimple hdetNonneg
  have hfull : HasFullRowRank (bandedMatrix b) :=
    bandedMatrix_hasFullRowRank_of_positive hb.1
  refine ⟨b, hb, hclose, hpattern, hTwo, hTNN, hfull, ?_⟩
  intro i₀ i₁ hi j₀ j₁ hj hminor
  exact bandedMatrix_nonstructural_twoMinor_pos hb i₀ i₁ hi j₀ j₁ hj hminor

/-- Theorem 20: every prescribed interior consecutive-minor zero pattern is
realized by positive coefficients arbitrarily close to the sine vector. -/
theorem arbitraryZeroPattern
    (hd : 2 ≤ d) (Z : Set (Fin (d - 1))) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ b : Fin (d + 1) → ℝ,
      StrictlyLogConcaveWithZeroBoundary b ∧
      ‖b - sineCoefficient d‖ < epsilon ∧
      (∀ i : Fin (d - 1),
        consecutiveDeterminant b ⟨i + 1, by omega⟩ = 0 ↔ i ∈ Z) ∧
      TNUpTo (bandedMatrix b) 2 ∧
      TotallyNonnegative (bandedMatrix b) ∧
      HasFullRowRank (bandedMatrix b) ∧
      ∀ (i₀ i₁ : Fin 3) (hi : i₀ < i₁)
        (j₀ j₁ : Fin (d + 3)) (hj : j₀ < j₁),
        IsNonstructuralTwoMinor (bandCoefficientVector b) i₀ i₁ j₀ j₁ →
          0 < orderedMinor (bandedMatrix b)
            (twoPointOrderEmbedding i₀ i₁ hi) (twoPointOrderEmbedding j₀ j₁ hj) := by
  exact arbitraryZeroPattern_of_equiv hd
    (sineJacobianContinuousLinearEquiv d hd)
    (consecutiveInteriorMap_hasStrictFDerivAt_equiv d hd) Z hepsilon

end

end ToeplitzPositroids.RankThree
