import ToeplitzPositroids.Edrei.FactorialKernelArbitrary
import ToeplitzPositroids.Edrei.FiniteFactorTN

/-!
# Support in the positive-exponential Edrei branch

The arbitrary reciprocal-factorial theorem supplies the exponential factor in
the finite Cauchy--Binet decomposition.  Total nonnegativity of the finite
factor then makes every structurally allowed full Edrei minor strictly positive.
-/

namespace ToeplitzPositroids

noncomputable section

/-- A positive exponential parameter makes every structurally allowed
exponential Toeplitz minor strictly positive. -/
theorem exponentialAllowedMinorsPositive_of_pos {gamma : ℝ} (hgamma : 0 < gamma) :
    FiniteEdreiData.ExponentialAllowedMinorsPositive gamma := by
  intro r rows cols hallowed
  exact exponentialToeplitzMinor_arbitraryRows_pos hgamma rows cols hallowed

namespace FiniteEdreiData

variable {p q : ℕ} (D : FiniteEdreiData p q)

/-- Namespaced form of arbitrary allowed exponential-minor positivity. -/
theorem exponentialAllowedMinorsPositive {gamma : ℝ} (hgamma : 0 < gamma) :
    ExponentialAllowedMinorsPositive gamma :=
  exponentialAllowedMinorsPositive_of_pos hgamma

/-- The unconditional positive-gamma branch of the finite Edrei support theorem. -/
theorem toeplitzMinor_pos_iff_componentwise_le_of_gamma_pos
    (hgamma : 0 < D.gamma)
    {r : ℕ} (rows cols : Fin r ↪o ℕ) :
    0 < D.toeplitzMinor rows cols ↔ ∀ i, rows i ≤ cols i := by
  exact D.toeplitzMinor_pos_iff_componentwise_le_of_factorHypotheses
    (exponentialAllowedMinorsPositive hgamma) D.finiteFactorMinorsNonnegative rows cols

end FiniteEdreiData

end

end ToeplitzPositroids
