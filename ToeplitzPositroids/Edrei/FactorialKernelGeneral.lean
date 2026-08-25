import ToeplitzPositroids.Edrei.FactorialKernelLGV
import Mathlib.Tactic

/-!
# Verified general cases of reciprocal-factorial positivity

This module consolidates the currently proved range of the generalized Pascal-minor problem:
all minors of order at most two, and minors of arbitrary order on consecutive row blocks.
-/

namespace ToeplitzPositroids

noncomputable section

/-- A structurally allowed reciprocal-factorial minor of order one is positive. -/
theorem factorialKernelMinor_one_pos (rows cols : Fin 1 ↪o ℕ)
    (hallowed : rows 0 ≤ cols 0) :
    0 < factorialKernelMinor rows cols := by
  rw [factorialKernelMinor, oneSidedToeplitzMinor, Matrix.det_fin_one]
  change 0 < factorialKernelCoefficient ((cols 0 : ℤ) - (rows 0 : ℤ))
  rw [factorialKernelCoefficient, if_pos (by omega), Int.toNat_sub]
  positivity

/-- Every structurally allowed reciprocal-factorial minor of order at most two is positive. -/
theorem factorialKernelMinor_pos_of_order_le_two {r : ℕ} (hr : r ≤ 2)
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i) :
    0 < factorialKernelMinor rows cols := by
  interval_cases r
  · simp [factorialKernelMinor, oneSidedToeplitzMinor]
  · exact factorialKernelMinor_one_pos rows cols (hallowed 0)
  · exact factorialKernelMinor_two_pos rows cols hallowed

/-- The corresponding exponential result in every order currently covered by the verified
factorial-kernel arguments. -/
theorem exponentialToeplitzMinor_pos_of_order_le_two {r : ℕ} (hr : r ≤ 2)
    {gamma : ℝ} (hgamma : 0 < gamma) (rows cols : Fin r ↪o ℕ)
    (hallowed : ∀ i, rows i ≤ cols i) :
    0 < exponentialToeplitzMinor gamma rows cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma rows cols).2
    (factorialKernelMinor_pos_of_order_le_two hr rows cols hallowed)

/-- A single theorem combining the small-order and arbitrary-order consecutive-row cases. -/
theorem factorialKernelMinor_pos_of_small_or_consecutiveRows {r : ℕ}
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (hshape : r ≤ 2 ∨ ∃ offset, rows = consecutiveNaturalRows offset r) :
    0 < factorialKernelMinor rows cols := by
  rcases hshape with hsmall | ⟨offset, rfl⟩
  · exact factorialKernelMinor_pos_of_order_le_two hsmall rows cols hallowed
  · apply factorialKernelMinor_consecutiveRows_pos cols
    intro i
    exact hallowed i

/-- Exponential positivity for the same verified general range. -/
theorem exponentialToeplitzMinor_pos_of_small_or_consecutiveRows {r : ℕ}
    {gamma : ℝ} (hgamma : 0 < gamma)
    (rows cols : Fin r ↪o ℕ) (hallowed : ∀ i, rows i ≤ cols i)
    (hshape : r ≤ 2 ∨ ∃ offset, rows = consecutiveNaturalRows offset r) :
    0 < exponentialToeplitzMinor gamma rows cols :=
  (exponentialToeplitzMinor_pos_iff_factorialKernelMinor_pos hgamma rows cols).2
    (factorialKernelMinor_pos_of_small_or_consecutiveRows rows cols hallowed hshape)

end

end ToeplitzPositroids
