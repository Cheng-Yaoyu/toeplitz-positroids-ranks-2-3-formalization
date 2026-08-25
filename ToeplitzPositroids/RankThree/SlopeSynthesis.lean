import ToeplitzPositroids.Geometry.ConvexChain
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Finite slope synthesis

This file formalizes the recurrence in Lemma 14 of the paper.  Instead of a
continuity argument, it uses an explicit smallness condition on the initial
parameter.  The horizontal increments then decrease, which simultaneously
keeps every denominator positive and bounds every constructed ratio.
-/

namespace ToeplitzPositroids.RankThree

open ToeplitzPositroids

noncomputable section

/-- One step of the ratio recurrence, with previous ratio `p`, current ratio `q`, and target
slope `s`. -/
def nextSynthesizedRatio (p q s : ℝ) : ℝ :=
  q + q * (q - p) / (s - q)

/-- Extend a finite slope family to natural-number indices.  Values outside its range are
irrelevant to the synthesis theorems. -/
def finiteSlopeValue {N : ℕ} (s : Fin N → ℝ) (j : ℕ) : ℝ :=
  if hj : j < N then s ⟨j, hj⟩ else 0

/-- Ratios generated from initial values `ε, 2ε` by the finite-slope recurrence. -/
def synthesizedRatio {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) : ℕ → ℝ
  | 0 => ε
  | 1 => 2 * ε
  | j + 2 => nextSynthesizedRatio (synthesizedRatio s ε j)
      (synthesizedRatio s ε (j + 1)) (finiteSlopeValue s j)

@[simp]
theorem synthesizedRatio_zero {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) :
    synthesizedRatio s ε 0 = ε :=
  rfl

@[simp]
theorem synthesizedRatio_one {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) :
    synthesizedRatio s ε 1 = 2 * ε :=
  rfl

@[simp]
theorem synthesizedRatio_add_two {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) :
    synthesizedRatio s ε (j + 2) =
      nextSynthesizedRatio (synthesizedRatio s ε j) (synthesizedRatio s ε (j + 1))
        (finiteSlopeValue s j) :=
  rfl

@[simp]
theorem finiteSlopeValue_apply {N : ℕ} (s : Fin N → ℝ) {j : ℕ} (hj : j < N) :
    finiteSlopeValue s j = s ⟨j, hj⟩ := by
  simp [finiteSlopeValue, hj]

/-- The explicit condition ensuring that all recurrence denominators stay positive. -/
def IsAdmissibleSynthesisEpsilon {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ j : Fin N, 2 * (N + 2 : ℝ) * ε < s j

/-- The algebraic hypotheses on a finite target-slope family. -/
def IsPositiveMonotoneSlopeFamily {N : ℕ} (s : Fin N → ℝ) : Prop :=
  (∀ j, 0 < s j) ∧ Monotone s

/-- The recurrence increment at step `j` has its cancellation-friendly form. -/
theorem synthesizedRatio_increment {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) {j : ℕ}
    (hj : j < N) :
    synthesizedRatio s ε (j + 2) - synthesizedRatio s ε (j + 1) =
      synthesizedRatio s ε (j + 1) *
        (synthesizedRatio s ε (j + 1) - synthesizedRatio s ε j) /
          (s ⟨j, hj⟩ - synthesizedRatio s ε (j + 1)) := by
  rw [synthesizedRatio_add_two, finiteSlopeValue_apply s hj]
  simp only [nextSynthesizedRatio]
  ring

/-- Positivity, decreasing increments, and a linear upper bound hold simultaneously throughout
the finite recurrence. -/
theorem synthesizedRatio_invariants {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    ∀ k : ℕ, k ≤ N →
      0 < synthesizedRatio s ε k ∧
        0 < synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k ∧
        synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k ≤ ε ∧
        synthesizedRatio s ε (k + 1) ≤ (k + 2 : ℝ) * ε := by
  intro k hk
  induction k with
  | zero =>
      refine ⟨hε.1, ?_, ?_, ?_⟩
      · simp only [synthesizedRatio]
        linarith [hε.1]
      · simp only [synthesizedRatio]
        ring_nf
        exact le_rfl
      · norm_num [synthesizedRatio]
  | succ k ih =>
      have hkN : k < N := by omega
      have hprev := ih (by omega)
      rcases hprev with ⟨hrPos, hΔPos, hΔLe, hrBound⟩
      have hcurPos : 0 < synthesizedRatio s ε (k + 1) := by linarith
      have hkBound : (k + 2 : ℝ) ≤ (N + 2 : ℝ) := by
        exact_mod_cast (show k + 2 ≤ N + 2 by omega)
      have hcurBound : synthesizedRatio s ε (k + 1) ≤ (N + 2 : ℝ) * ε := by
        have hmul := mul_le_mul_of_nonneg_right hkBound hε.1.le
        exact hrBound.trans hmul
      have htwocur : 2 * synthesizedRatio s ε (k + 1) < s ⟨k, hkN⟩ := by
        have hsmall := hε.2 ⟨k, hkN⟩
        nlinarith
      have hdenPos : 0 < s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1) := by
        linarith
      have hfactorPos : 0 <
          synthesizedRatio s ε (k + 1) /
            (s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1)) :=
        div_pos hcurPos hdenPos
      have hfactorLe :
          synthesizedRatio s ε (k + 1) /
              (s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1)) ≤ 1 := by
        rw [div_le_one hdenPos]
        linarith
      have hinc := synthesizedRatio_increment s ε hkN
      have hnextΔPos :
          0 < synthesizedRatio s ε (k + 2) - synthesizedRatio s ε (k + 1) := by
        rw [hinc]
        exact div_pos (mul_pos hcurPos hΔPos) hdenPos
      have hnextΔLe :
          synthesizedRatio s ε (k + 2) - synthesizedRatio s ε (k + 1) ≤ ε := by
        rw [hinc]
        have hrearrange :
            synthesizedRatio s ε (k + 1) *
                  (synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k) /
                (s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1)) =
              (synthesizedRatio s ε (k + 1) /
                  (s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1))) *
                (synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k) := by
          ring
        rw [hrearrange]
        calc
          synthesizedRatio s ε (k + 1) /
                (s ⟨k, hkN⟩ - synthesizedRatio s ε (k + 1)) *
              (synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k) ≤
              1 * (synthesizedRatio s ε (k + 1) - synthesizedRatio s ε k) :=
            mul_le_mul_of_nonneg_right hfactorLe hΔPos.le
          _ ≤ ε := by simpa using hΔLe
      refine ⟨hcurPos, hnextΔPos, hnextΔLe, ?_⟩
      have hbound :
          synthesizedRatio s ε (k + 2) ≤ (k + 3 : ℝ) * ε := by
        calc
          synthesizedRatio s ε (k + 2) ≤ synthesizedRatio s ε (k + 1) + ε := by
            linarith
          _ ≤ (k + 3 : ℝ) * ε := by
            nlinarith [hε.1]
      rw [show k + 1 + 1 = k + 2 by omega]
      norm_num only [Nat.cast_add, Nat.cast_one]
      ring_nf at hbound ⊢
      exact hbound

/-- Every denominator actually used by the recurrence is strictly positive. -/
theorem synthesizedRatio_denominator_pos {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {j : ℕ} (hj : j < N) :
    0 < s ⟨j, hj⟩ - synthesizedRatio s ε (j + 1) := by
  have hinv := synthesizedRatio_invariants hε j hj.le
  have hjBound : (j + 2 : ℝ) ≤ (N + 2 : ℝ) := by
    exact_mod_cast (show j + 2 ≤ N + 2 by omega)
  have hcurBound : synthesizedRatio s ε (j + 1) ≤ (N + 2 : ℝ) * ε :=
    hinv.2.2.2.trans (mul_le_mul_of_nonneg_right hjBound hε.1.le)
  have := hε.2 ⟨j, hj⟩
  linarith

/-- The synthesized ratios are strictly increasing throughout the required finite range. -/
theorem synthesizedRatio_strictMonoOn {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) :
    ∀ {i j : ℕ}, i < j → j < N + 2 → synthesizedRatio s ε i < synthesizedRatio s ε j := by
  intro i j hij hjN
  have hmono : StrictMonoOn (synthesizedRatio s ε) (Set.Iio (N + 2)) := by
    apply strictMonoOn_of_lt_succ Set.ordConnected_Iio
    intro k _ hk hk1
    have hkN : k ≤ N := by
      change k + 1 < N + 2 at hk1
      omega
    have hinv := synthesizedRatio_invariants hε k hkN
    change synthesizedRatio s ε k < synthesizedRatio s ε (k + 1)
    exact sub_pos.mp hinv.2.1
  exact hmono (Set.mem_Iio.mpr (hij.trans hjN)) (Set.mem_Iio.mpr hjN) hij

/-- Every ratio in the synthesized finite segment is positive. -/
theorem synthesizedRatio_pos_of_lt {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) {k : ℕ} (hk : k < N + 2) :
    0 < synthesizedRatio s ε k := by
  by_cases hk0 : k = 0
  · subst k
    simpa using hε.1
  · have h0k : 0 < k := Nat.pos_of_ne_zero hk0
    calc
      0 < synthesizedRatio s ε 0 := by simpa using hε.1
      _ < synthesizedRatio s ε k := synthesizedRatio_strictMonoOn hε h0k hk

/-- Coordinates of the normalized ratio point `Q_(j+1)`. -/
def synthesizedPointX {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) : ℝ :=
  synthesizedRatio s ε (j + 1)

/-- Second coordinates of the normalized ratio point `Q_(j+1)`. -/
def synthesizedPointY {N : ℕ} (s : Fin N → ℝ) (ε : ℝ) (j : ℕ) : ℝ :=
  synthesizedRatio s ε j * synthesizedRatio s ε (j + 1)

/-- The recurrence equation gives the requested affine slope for one abstract step. -/
theorem nextSynthesizedRatio_slope (p q target : ℝ) (hq : q ≠ 0) (hΔ : q - p ≠ 0)
    (hden : target - q ≠ 0) :
    (q * nextSynthesizedRatio p q target - p * q) /
        (nextSynthesizedRatio p q target - q) = target := by
  have hstep : nextSynthesizedRatio p q target - q = q * (q - p) / (target - q) := by
    simp only [nextSynthesizedRatio]
    ring
  have hstep0 : nextSynthesizedRatio p q target - q ≠ 0 := by
    rw [hstep]
    exact div_ne_zero (mul_ne_zero hq hΔ) hden
  apply (div_eq_iff hstep0).2
  rw [hstep]
  simp only [nextSynthesizedRatio]
  field_simp [hden]
  ring

/-- The ratio recurrence realizes the prescribed slope exactly. -/
theorem synthesizedPoint_edgeSlope {N : ℕ} {s : Fin N → ℝ} {ε : ℝ}
    (hε : IsAdmissibleSynthesisEpsilon s ε) (j : Fin N) :
    edgeSlope (synthesizedPointX s ε) (synthesizedPointY s ε) j.val = s j := by
  have hden := synthesizedRatio_denominator_pos hε j.isLt
  have hinv := synthesizedRatio_invariants hε j.val j.isLt.le
  have hcur : synthesizedRatio s ε (j.val + 1) ≠ 0 := by linarith [hinv.1, hinv.2.1]
  have hΔ := hinv.2.1
  rw [edgeSlope, chordSlope, synthesizedPointX, synthesizedPointY]
  change
    (synthesizedRatio s ε (j.val + 1) * synthesizedRatio s ε (j.val + 2) -
        synthesizedRatio s ε j.val * synthesizedRatio s ε (j.val + 1)) /
      (synthesizedRatio s ε (j.val + 2) - synthesizedRatio s ε (j.val + 1)) = s j
  rw [synthesizedRatio_add_two, finiteSlopeValue_apply s j.isLt]
  exact nextSynthesizedRatio_slope _ _ _ hcur hΔ.ne' hden.ne'

/-- Every positive weakly increasing finite slope family admits an explicit admissible initial
parameter.  For a nonempty family, the chosen value is
`s 0 / (4 * (N + 2))`; the empty family uses `1`. -/
theorem exists_admissibleSynthesisEpsilon {N : ℕ} {s : Fin N → ℝ}
    (hs : IsPositiveMonotoneSlopeFamily s) :
    ∃ ε : ℝ, IsAdmissibleSynthesisEpsilon s ε := by
  by_cases hN : N = 0
  · subst N
    refine ⟨1, zero_lt_one, ?_⟩
    intro j
    exact Fin.elim0 j
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let first : Fin N := ⟨0, hNpos⟩
    let ε : ℝ := s first / (4 * (N + 2 : ℝ))
    refine ⟨ε, ?_, ?_⟩
    · dsimp [ε]
      exact div_pos (hs.1 first) (mul_pos (by norm_num) (by positivity))
    · intro j
      have hfirst : s first ≤ s j := hs.2 (Nat.zero_le j.val)
      have hden : (4 * (N + 2 : ℝ)) ≠ 0 := by positivity
      have heq : 2 * (N + 2 : ℝ) * ε = s first / 2 := by
        dsimp [ε]
        field_simp
        ring
      rw [heq]
      linarith [hs.1 first]

/-- Fully packaged finite-slope synthesis.  The resulting ratios and point abscissae strictly
increase, the point edges have exactly the requested slopes, and those slopes are therefore
weakly increasing along the constructed chain. -/
theorem exists_finiteSlopeSynthesis {N : ℕ} (s : Fin N → ℝ)
    (hs : IsPositiveMonotoneSlopeFamily s) :
    ∃ ε : ℝ,
      IsAdmissibleSynthesisEpsilon s ε ∧
        StrictlyIncreasingUpTo (synthesizedRatio s ε) (N + 2) ∧
        (∀ k : ℕ, k < N + 2 → 0 < synthesizedRatio s ε k) ∧
        StrictlyIncreasingUpTo (synthesizedPointX s ε) (N + 1) ∧
        (∀ j : Fin N,
          edgeSlope (synthesizedPointX s ε) (synthesizedPointY s ε) j.val = s j) ∧
        SlopesMonotoneUpTo (synthesizedPointX s ε) (synthesizedPointY s ε) (N + 1) := by
  obtain ⟨ε, hε⟩ := exists_admissibleSynthesisEpsilon hs
  refine ⟨ε, hε, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij hjN
    exact synthesizedRatio_strictMonoOn hε hij hjN
  · intro k hk
    exact synthesizedRatio_pos_of_lt hε hk
  · intro i j hij hjN
    unfold synthesizedPointX
    apply synthesizedRatio_strictMonoOn hε
    · omega
    · omega
  · exact synthesizedPoint_edgeSlope hε
  · intro i j hij hjN
    have hiN : i < N := by omega
    have hjN' : j < N := by omega
    have hiSlope := synthesizedPoint_edgeSlope hε ⟨i, hiN⟩
    have hjSlope := synthesizedPoint_edgeSlope hε ⟨j, hjN'⟩
    rw [hiSlope, hjSlope]
    exact hs.2 (by simpa using hij)

/-- Recover the shifted positive Toeplitz coefficients from a ratio sequence.  Index `0`
represents `a_(-2)`, index `1` represents `a_(-1)`, and the remaining values follow the paper's
recurrence `a_(j-1) = a_(j-2) / r_j`. -/
def recoveredCoefficient (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => r 0
  | 1 => 1
  | j + 2 => recoveredCoefficient r (j + 1) / r (j + 1)

@[simp]
theorem recoveredCoefficient_zero (r : ℕ → ℝ) : recoveredCoefficient r 0 = r 0 :=
  rfl

@[simp]
theorem recoveredCoefficient_one (r : ℕ → ℝ) : recoveredCoefficient r 1 = 1 :=
  rfl

@[simp]
theorem recoveredCoefficient_add_two (r : ℕ → ℝ) (j : ℕ) :
    recoveredCoefficient r (j + 2) = recoveredCoefficient r (j + 1) / r (j + 1) :=
  rfl

/-- Positive ratios recover positive coefficients. -/
theorem recoveredCoefficient_pos {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) :
    ∀ j, 0 < recoveredCoefficient r j := by
  intro j
  induction j with
  | zero => simpa using hr 0
  | succ j ih =>
      cases j with
      | zero => simp
      | succ j =>
          rw [show j + 1 + 1 = j + 2 by omega, recoveredCoefficient_add_two]
          exact div_pos ih (hr (j + 1))

/-- Coefficient recovery has the prescribed adjacent ratios. -/
theorem recoveredCoefficient_div_succ {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (j : ℕ) :
    recoveredCoefficient r j / recoveredCoefficient r (j + 1) = r j := by
  cases j with
  | zero => simp [recoveredCoefficient]
  | succ j =>
      have hcoeff : recoveredCoefficient r (j + 1) ≠ 0 :=
        (recoveredCoefficient_pos hr (j + 1)).ne'
      have hratio : r (j + 1) ≠ 0 := (hr (j + 1)).ne'
      rw [show j + 1 + 1 = j + 2 by omega, recoveredCoefficient_add_two]
      field_simp

/-- A weakly increasing positive ratio sequence recovers a log-concave coefficient sequence. -/
theorem recoveredCoefficient_logConcave {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hrMono : ∀ j, r j ≤ r (j + 1)) (j : ℕ) :
    recoveredCoefficient r j * recoveredCoefficient r (j + 2) ≤
      recoveredCoefficient r (j + 1) ^ 2 := by
  have hApos : 0 ≤ recoveredCoefficient r (j + 1) :=
    (recoveredCoefficient_pos hr (j + 1)).le
  have hBpos : 0 ≤ recoveredCoefficient r (j + 2) :=
    (recoveredCoefficient_pos hr (j + 2)).le
  have hjEq : recoveredCoefficient r j = r j * recoveredCoefficient r (j + 1) := by
    have hnext := (recoveredCoefficient_pos hr (j + 1)).ne'
    have hratio := recoveredCoefficient_div_succ hr j
    field_simp at hratio
    nlinarith
  have hnextEq : recoveredCoefficient r (j + 1) =
      r (j + 1) * recoveredCoefficient r (j + 2) := by
    have hnext := (recoveredCoefficient_pos hr (j + 2)).ne'
    have hratio := recoveredCoefficient_div_succ hr (j + 1)
    field_simp at hratio
    nlinarith
  have hscaled : r j * recoveredCoefficient r (j + 2) ≤
      r (j + 1) * recoveredCoefficient r (j + 2) :=
    mul_le_mul_of_nonneg_right (hrMono j) hBpos
  calc
    recoveredCoefficient r j * recoveredCoefficient r (j + 2) =
        recoveredCoefficient r (j + 1) *
          (r j * recoveredCoefficient r (j + 2)) := by rw [hjEq]; ring
    _ ≤ recoveredCoefficient r (j + 1) *
        (r (j + 1) * recoveredCoefficient r (j + 2)) :=
      mul_le_mul_of_nonneg_left hscaled hApos
    _ = recoveredCoefficient r (j + 1) ^ 2 := by rw [← hnextEq]; ring

end


end ToeplitzPositroids.RankThree
