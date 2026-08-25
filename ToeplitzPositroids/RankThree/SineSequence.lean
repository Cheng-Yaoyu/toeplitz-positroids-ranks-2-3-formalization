import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The sine coefficient sequence

This file develops the trigonometric identities used at the two-sided sine base
point.  The coefficient with finite index `t` is
`sin ((t + 1) * π / (d + 2))`.
-/

namespace ToeplitzPositroids.RankThree

noncomputable section

/-- The angle `π / (d + 2)` used by the sine base point. -/
def sineAngle (d : ℕ) : ℝ :=
  Real.pi / (d + 2 : ℝ)

/-- The finite sine vector `b⁽⁰⁾`. -/
def sineCoefficient (d : ℕ) (t : Fin (d + 1)) : ℝ :=
  Real.sin ((t + 1 : ℝ) * sineAngle d)

theorem sineAngle_pos (d : ℕ) : 0 < sineAngle d := by
  unfold sineAngle
  positivity

theorem sineAngle_lt_pi (d : ℕ) : sineAngle d < Real.pi := by
  unfold sineAngle
  have hd0 : (0 : ℝ) ≤ d := by positivity
  have hd : (1 : ℝ) < d + 2 := by linarith
  have hpi := Real.pi_pos
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < d + 2)]
  nlinarith

/-- Every entry of the finite sine vector is positive. -/
theorem sineCoefficient_pos (d : ℕ) (t : Fin (d + 1)) :
    0 < sineCoefficient d t := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (by positivity) (sineAngle_pos d)
  · have ht : (t.val + 1 : ℝ) < d + 2 := by
      have hnat : t.val + 1 < d + 2 := by omega
      exact_mod_cast hnat
    have hden : (0 : ℝ) < d + 2 := by positivity
    unfold sineAngle
    rw [← mul_div_assoc, div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]

/-- A trigonometric sequence with fixed step satisfies the required second-order recurrence. -/
theorem sin_add_eq_two_cos_mul_sin_sub_sin_sub (x θ : ℝ) :
    Real.sin (x + θ) = 2 * Real.cos θ * Real.sin x - Real.sin (x - θ) := by
  rw [Real.sin_add, Real.sin_sub]
  ring

/-- The log-concavity defect of a sine progression is independent of its position. -/
theorem sin_sq_sub_sin_sub_mul_sin_add (x θ : ℝ) :
    Real.sin x ^ 2 - Real.sin (x - θ) * Real.sin (x + θ) = Real.sin θ ^ 2 := by
  rw [Real.sin_sub, Real.sin_add]
  have hx := Real.sin_sq_add_cos_sq x
  have hθ := Real.sin_sq_add_cos_sq θ
  nlinarith

/-- Consecutive entries of the finite sine vector satisfy the paper's recurrence. -/
theorem sineCoefficient_recurrence (d : ℕ) {t : ℕ} (ht : t + 2 < d + 1) :
    sineCoefficient d ⟨t + 2, ht⟩ =
      2 * Real.cos (sineAngle d) * sineCoefficient d ⟨t + 1, by omega⟩ -
        sineCoefficient d ⟨t, by omega⟩ := by
  simp only [sineCoefficient, Nat.cast_add, Nat.cast_ofNat]
  convert sin_add_eq_two_cos_mul_sin_sub_sin_sub
    (((t : ℝ) + 2) * sineAngle d) (sineAngle d) using 1
  all_goals ring_nf

/-- Every interior coefficient has the constant strict log-concavity defect `sin² θ`. -/
theorem sineCoefficient_logConcavity_defect (d : ℕ) {t : ℕ}
    (ht0 : 0 < t) (htd : t + 1 < d + 1) :
    sineCoefficient d ⟨t, by omega⟩ ^ 2 -
        sineCoefficient d ⟨t - 1, by omega⟩ * sineCoefficient d ⟨t + 1, by omega⟩ =
      Real.sin (sineAngle d) ^ 2 := by
  simp only [sineCoefficient, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub (by omega : 1 ≤ t)]
  convert sin_sq_sub_sin_sub_mul_sin_add
    (((t : ℝ) + 1) * sineAngle d) (sineAngle d) using 1
  all_goals ring_nf

/-- The first sine coefficient is `sin θ`. -/
@[simp]
theorem sineCoefficient_zero (d : ℕ) :
    sineCoefficient d 0 = Real.sin (sineAngle d) := by
  simp [sineCoefficient]

/-- The last sine coefficient also equals `sin θ`. -/
theorem sineCoefficient_last (d : ℕ) :
    sineCoefficient d (Fin.last d) = Real.sin (sineAngle d) := by
  change Real.sin (((d : ℝ) + 1) * sineAngle d) = Real.sin (sineAngle d)
  have hangle : ((d : ℝ) + 1) * sineAngle d = Real.pi - sineAngle d := by
    unfold sineAngle
    field_simp
    ring
  rw [hangle, Real.sin_pi_sub]

end

end ToeplitzPositroids.RankThree
