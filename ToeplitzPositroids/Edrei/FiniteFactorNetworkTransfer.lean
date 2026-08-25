import ToeplitzPositroids.Edrei.FiniteFactorNetwork
import Mathlib.Data.Matrix.Basic

/-!
# Transfer matrices of finite-factor network chips

This file gives the algebraic transfer matrices used in the single-path coefficient proof.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids Matrix

/-- Matrix of one elementary network chip. -/
def FiniteEdreiData.networkStageMatrix {p q : ℕ} (D : FiniteEdreiData p q)
    (N t : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  fun x y ↦ FiniteEdreiData.networkStepWeight D N t x y

/-- Ordered product of the first `L` chip matrices. -/
def FiniteEdreiData.networkTransferPrefix {p q : ℕ} (D : FiniteEdreiData p q)
    (N : ℕ) : (L : ℕ) → Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ
  | 0 => 1
  | L + 1 => FiniteEdreiData.networkTransferPrefix D N L *
      FiniteEdreiData.networkStageMatrix D N L

/-- Transfer matrix of the whole finite-factor network. -/
def FiniteEdreiData.networkTransfer {p q : ℕ} (D : FiniteEdreiData p q)
    (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  FiniteEdreiData.networkTransferPrefix D N (finiteFactorStageCount p q N)

@[simp]
theorem FiniteEdreiData.networkStageMatrix_stay {p q : ℕ}
    (D : FiniteEdreiData p q) (N t : ℕ) (x : Fin (N + 1)) :
    FiniteEdreiData.networkStageMatrix D N t x x = 1 := by
  simp [FiniteEdreiData.networkStageMatrix, FiniteEdreiData.networkStepWeight]

/-- A beta chip has its beta parameter on every available superdiagonal step. -/
theorem FiniteEdreiData.networkStageMatrix_beta_succ {p q : ℕ}
    (D : FiniteEdreiData p q) (N : ℕ) (t : Fin q) (x : Fin N) :
    FiniteEdreiData.networkStageMatrix D N t.val x.castSucc x.succ = D.beta t := by
  simp [FiniteEdreiData.networkStageMatrix, FiniteEdreiData.networkStepWeight,
    t.isLt]

end ToeplitzPositroids.Edrei
