import ToeplitzPositroids.RankThree.OrderTwo
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Equality in order-two Toeplitz minors

This file completes the equality statement in Lemma 5.  For a nonstructural
two-by-two minor, equality is equivalent to constancy of every adjacent
coefficient ratio across the full interval between its two extreme entries.
-/

namespace ToeplitzPositroids

variable {n : ℕ} {a : Fin (n + 2) → ℝ}

/-- Equality in a positive two-step Toeplitz inequality is equivalent to
constancy of the two overlapping strings of adjacent ratios. -/
theorem twoStepToeplitzDifference_eq_zero_iff_ratio_const
    (hnonneg : ∀ k, 0 ≤ a k) (hsupport : HasIntervalPositiveSupport a)
    (hlog : DiscretelyLogConcave a) {p q : Fin n} (hpq : p < q)
    (hleft : 0 < a p.castSucc.castSucc) (hright : 0 < a q.succ.succ) :
    a p.succ.succ * a q.castSucc.castSucc -
        a q.succ.succ * a p.castSucc.castSucc = 0 ↔
      ∀ t : Fin (n + 1), p.val ≤ t.val → t.val ≤ q.val + 1 →
        coefficientRatio a t = coefficientRatio a p.castSucc := by
  have hpos : ∀ t : Fin (n + 2), p.val ≤ t.val → t.val ≤ q.val + 2 → 0 < a t := by
    intro t hpt htq
    apply (hasIntervalPositiveSupport_iff a).mp hsupport
      p.castSucc.castSucc q.succ.succ t hleft hright
    · change p.val ≤ t.val
      exact hpt
    · change t.val ≤ q.val + 2
      exact htq
  have hp₁ : 0 < a p.succ.castSucc := by
    apply hpos p.succ.castSucc
    · change p.val ≤ p.val + 1
      omega
    · change p.val + 1 ≤ q.val + 2
      omega
  have hp₂ : 0 < a p.succ.succ := by
    apply hpos p.succ.succ
    · change p.val ≤ p.val + 2
      omega
    · change p.val + 2 ≤ q.val + 2
      omega
  have hq₁ : 0 < a q.castSucc.succ := by
    apply hpos q.castSucc.succ
    · change p.val ≤ q.val + 1
      omega
    · change q.val + 1 ≤ q.val + 2
      omega
  have hpcenter : p.castSucc.succ = p.succ.castSucc := by
    apply Fin.ext
    rfl
  have hqcenter : q.castSucc.succ = q.succ.castSucc := by
    apply Fin.ext
    rfl
  let d₀ := a p.castSucc.succ * a q.castSucc.castSucc -
    a q.castSucc.succ * a p.castSucc.castSucc
  let d₁ := a p.succ.succ * a q.succ.castSucc -
    a q.succ.succ * a p.succ.castSucc
  have hd₀ : 0 ≤ d₀ := by
    dsimp only [d₀]
    exact oneStepToeplitzDifference_nonneg hnonneg hsupport hlog
      (p := p.castSucc) (q := q.castSucc) (by simpa using hpq)
  have hd₁ : 0 ≤ d₁ := by
    dsimp only [d₁]
    exact oneStepToeplitzDifference_nonneg hnonneg hsupport hlog
      (p := p.succ) (q := q.succ) (by simpa using hpq)
  have heq₀ : d₀ = 0 ↔
      ∀ t : Fin (n + 1), p.castSucc ≤ t → t ≤ q.castSucc →
        coefficientRatio a t = coefficientRatio a p.castSucc := by
    dsimp only [d₀]
    exact oneStepToeplitzDifference_eq_zero_iff_ratio_const hsupport hlog
      (show p.castSucc ≤ q.castSucc by simpa using hpq.le) hleft hq₁
  have heq₁ : d₁ = 0 ↔
      ∀ t : Fin (n + 1), p.succ ≤ t → t ≤ q.succ →
        coefficientRatio a t = coefficientRatio a p.succ := by
    dsimp only [d₁]
    exact oneStepToeplitzDifference_eq_zero_iff_ratio_const hsupport hlog
      (show p.succ ≤ q.succ by simpa using hpq.le) hp₁ hright
  have hoverlap :
      a p.succ.castSucc *
          (a p.succ.succ * a q.castSucc.castSucc -
            a q.succ.succ * a p.castSucc.castSucc) =
        a p.succ.succ * d₀ + a p.castSucc.castSucc * d₁ := by
    dsimp only [d₀, d₁]
    rw [hpcenter, hqcenter]
    ring
  constructor
  · intro hminor
    have hsum : a p.succ.succ * d₀ + a p.castSucc.castSucc * d₁ = 0 := by
      rw [← hoverlap, hminor, mul_zero]
    have hterm₀ : 0 ≤ a p.succ.succ * d₀ := mul_nonneg hp₂.le hd₀
    have hterm₁ : 0 ≤ a p.castSucc.castSucc * d₁ := mul_nonneg hleft.le hd₁
    have hterm₀zero : a p.succ.succ * d₀ = 0 := by linarith
    have hterm₁zero : a p.castSucc.castSucc * d₁ = 0 := by linarith
    have hd₀zero : d₀ = 0 :=
      (mul_eq_zero.mp hterm₀zero).resolve_left (ne_of_gt hp₂)
    have hd₁zero : d₁ = 0 :=
      (mul_eq_zero.mp hterm₁zero).resolve_left (ne_of_gt hleft)
    have hconst₀ := heq₀.mp hd₀zero
    have hconst₁ := heq₁.mp hd₁zero
    intro t hpt htq
    by_cases ht : t.val ≤ q.val
    · apply hconst₀ t
      · change p.val ≤ t.val
        exact hpt
      · change t.val ≤ q.val
        exact ht
    · have htval : t.val = q.val + 1 := by omega
      have hteq : t = q.succ := by
        apply Fin.ext
        exact htval
      subst t
      have hrightConst := hconst₁ q.succ (by simpa using hpq.le) le_rfl
      have hjoin := hconst₀ p.succ (by
        change p.val ≤ p.val + 1
        omega) (by
        change p.val + 1 ≤ q.val
        omega)
      exact hrightConst.trans hjoin
  · intro hconst
    have hconst₀ : ∀ t : Fin (n + 1), p.castSucc ≤ t → t ≤ q.castSucc →
        coefficientRatio a t = coefficientRatio a p.castSucc := by
      intro t hpt htq
      apply hconst t
      · exact hpt
      · change t.val ≤ q.val at htq
        omega
    have hp₁const := hconst p.succ (by
      change p.val ≤ p.val + 1
      omega) (by
      change p.val + 1 ≤ q.val + 1
      omega)
    have hconst₁ : ∀ t : Fin (n + 1), p.succ ≤ t → t ≤ q.succ →
        coefficientRatio a t = coefficientRatio a p.succ := by
      intro t hpt htq
      apply (hconst t ?_ ?_).trans hp₁const.symm
      · change p.val + 1 ≤ t.val at hpt
        omega
      · change t.val ≤ q.val + 1 at htq
        exact htq
    have hd₀zero := heq₀.mpr hconst₀
    have hd₁zero := heq₁.mpr hconst₁
    have hweighted : a p.succ.castSucc *
        (a p.succ.succ * a q.castSucc.castSucc -
          a q.succ.succ * a p.castSucc.castSucc) = 0 := by
      rw [hoverlap, hd₀zero, hd₁zero]
      ring
    exact (mul_eq_zero.mp hweighted).resolve_left (ne_of_gt hp₁)

/-- A selected two-by-two Toeplitz minor is nonstructural when all four of its
matrix entries are positive. -/
def IsNonstructuralTwoMinor (a : Fin (n + 2) → ℝ) (i₀ i₁ : Fin 3)
    (j₀ j₁ : Fin n) : Prop :=
  0 < a (finiteToeplitzIndex i₀ j₀) ∧
    0 < a (finiteToeplitzIndex i₀ j₁) ∧
    0 < a (finiteToeplitzIndex i₁ j₀) ∧
    0 < a (finiteToeplitzIndex i₁ j₁)

/-- The first coefficient-ratio index in a two-by-two minor.  It is the
coefficient index of the lower-left matrix entry. -/
def minorRatioStart (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ : Fin n) : Fin (n + 1) :=
  ⟨finiteToeplitzIndex i₁ j₀, by
    simp only [finiteToeplitzIndex_val]
    omega⟩

@[simp]
theorem minorRatioStart_val (i₀ i₁ : Fin 3) (hi : i₀ < i₁) (j₀ : Fin n) :
    (minorRatioStart i₀ i₁ hi j₀ : ℕ) = finiteToeplitzIndex i₁ j₀ :=
  rfl

/-- Equality criterion for every nonstructural two-by-two Toeplitz minor.

The ratio interval begins at the lower-left coefficient and ends immediately
before the upper-right coefficient.  In the paper's integer labels this is the
range `ρ_{x-h+1}, ..., ρ_{x+ℓ}` in equation (4.5).  The proof treats row
distances one and two; the latter is the union of two overlapping one-step
ratio intervals. -/
theorem rankThreeToeplitz_nonstructural_minor_eq_zero_iff_ratio_const
    (hnonneg : ∀ k, 0 ≤ a k) (hsupport : HasIntervalPositiveSupport a)
    (hlog : DiscretelyLogConcave a) (i₀ i₁ : Fin 3) (hi : i₀ < i₁)
    (j₀ j₁ : Fin n) (hj : j₀ < j₁)
    (hminor : IsNonstructuralTwoMinor a i₀ i₁ j₀ j₁) :
    orderedMinor (rankThreeToeplitz a) (twoPointOrderEmbedding i₀ i₁ hi)
        (twoPointOrderEmbedding j₀ j₁ hj) = 0 ↔
      ∀ t : Fin (n + 1), (minorRatioStart i₀ i₁ hi j₀).val ≤ t.val →
        t.val < (finiteToeplitzIndex i₀ j₁).val →
          coefficientRatio a t = coefficientRatio a (minorRatioStart i₀ i₁ hi j₀) := by
  rw [rankThreeToeplitz_orderedMinor_two]
  have hhigh := hminor.2.1
  have hlow := hminor.2.2.1
  fin_cases i₀ <;> fin_cases i₁ <;> simp at hi
  · have h := oneStepToeplitzDifference_eq_zero_iff_ratio_const hsupport hlog
      (p := j₀.succ) (q := j₁.succ) (by simpa using hj.le)
      (by simpa [finiteToeplitzIndex] using hlow)
      (by simpa [finiteToeplitzIndex] using hhigh)
    constructor
    · intro hzero t hstart hend
      have hconst := h.mp (by simpa [finiteToeplitzIndex] using hzero)
      have hstart' : j₀.succ ≤ t := by
        change j₀.val + 1 ≤ t.val
        simp only [minorRatioStart_val, finiteToeplitzIndex_val] at hstart
        omega
      have hend' : t ≤ j₁.succ := by
        change t.val ≤ j₁.val + 1
        simp only [finiteToeplitzIndex_val] at hend
        omega
      simpa [coefficientRatio, minorRatioStart, finiteToeplitzIndex] using
        hconst t hstart' hend'
    · intro hconst
      have hconst' : ∀ t : Fin (n + 1), j₀.succ ≤ t → t ≤ j₁.succ →
          coefficientRatio a t = coefficientRatio a j₀.succ := by
        intro t hstart hend
        have hstart' : (minorRatioStart (0 : Fin 3) 1 (by decide) j₀).val ≤ t.val := by
          simp only [minorRatioStart_val, finiteToeplitzIndex_val]
          change j₀.val + 1 ≤ t.val at hstart
          exact hstart
        have hend' : t.val < (finiteToeplitzIndex (0 : Fin 3) j₁).val := by
          simp only [finiteToeplitzIndex_val]
          change t.val ≤ j₁.val + 1 at hend
          omega
        simpa [coefficientRatio, minorRatioStart, finiteToeplitzIndex] using
          hconst t hstart' hend'
      simpa [finiteToeplitzIndex] using h.mpr hconst'
  · have h := twoStepToeplitzDifference_eq_zero_iff_ratio_const
      hnonneg hsupport hlog hj
      (by simpa [finiteToeplitzIndex] using hlow)
      (by simpa [finiteToeplitzIndex] using hhigh)
    constructor
    · intro hzero t hstart hend
      have hconst := h.mp (by simpa [finiteToeplitzIndex] using hzero)
      have hstart' : j₀.val ≤ t.val := by
        simp only [minorRatioStart_val, finiteToeplitzIndex_val] at hstart
        exact hstart
      have hend' : t.val ≤ j₁.val + 1 := by
        simp only [finiteToeplitzIndex_val] at hend
        omega
      simpa [coefficientRatio, minorRatioStart, finiteToeplitzIndex] using
        hconst t hstart' hend'
    · intro hconst
      have hconst' : ∀ t : Fin (n + 1), j₀.val ≤ t.val → t.val ≤ j₁.val + 1 →
          coefficientRatio a t = coefficientRatio a j₀.castSucc := by
        intro t hstart hend
        have hstart' : (minorRatioStart (0 : Fin 3) 2 (by decide) j₀).val ≤ t.val := by
          simpa only [minorRatioStart_val, finiteToeplitzIndex_val] using hstart
        have hend' : t.val < (finiteToeplitzIndex (0 : Fin 3) j₁).val := by
          simp only [finiteToeplitzIndex_val]
          omega
        simpa [coefficientRatio, minorRatioStart, finiteToeplitzIndex] using
          hconst t hstart' hend'
      simpa [finiteToeplitzIndex] using h.mpr hconst'
  · have h := oneStepToeplitzDifference_eq_zero_iff_ratio_const hsupport hlog
      (p := j₀.castSucc) (q := j₁.castSucc) (by simpa using hj.le)
      (by simpa [finiteToeplitzIndex] using hlow)
      (by simpa [finiteToeplitzIndex] using hhigh)
    simpa [finiteToeplitzIndex, minorRatioStart] using h

/-- The explicit finite-index form of the equality criterion in equation (4.5).

The four factors are the entries at the northwest, southeast, northeast, and
southwest corners of the selected Toeplitz submatrix.  The stated ratio range
is precisely the full range between the southwest and northeast coefficient
indices. -/
theorem rankThreeToeplitz_nonstructural_difference_eq_zero_iff_ratio_const
    (hnonneg : ∀ k, 0 ≤ a k) (hsupport : HasIntervalPositiveSupport a)
    (hlog : DiscretelyLogConcave a) (i₀ i₁ : Fin 3) (hi : i₀ < i₁)
    (j₀ j₁ : Fin n) (hj : j₀ < j₁)
    (hminor : IsNonstructuralTwoMinor a i₀ i₁ j₀ j₁) :
    a (finiteToeplitzIndex i₀ j₀) * a (finiteToeplitzIndex i₁ j₁) -
        a (finiteToeplitzIndex i₀ j₁) * a (finiteToeplitzIndex i₁ j₀) = 0 ↔
      ∀ t : Fin (n + 1), (minorRatioStart i₀ i₁ hi j₀).val ≤ t.val →
        t.val < (finiteToeplitzIndex i₀ j₁).val →
          coefficientRatio a t = coefficientRatio a (minorRatioStart i₀ i₁ hi j₀) := by
  have h := rankThreeToeplitz_nonstructural_minor_eq_zero_iff_ratio_const
    hnonneg hsupport hlog i₀ i₁ hi j₀ j₁ hj hminor
  rw [rankThreeToeplitz_orderedMinor_two] at h
  exact h

end ToeplitzPositroids
