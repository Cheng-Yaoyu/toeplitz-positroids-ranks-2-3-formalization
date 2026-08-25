import ToeplitzPositroids.Edrei.FormalSeries
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# The finite layered network for finite Edrei factors

For a truncation with wires `0, …, N`, every beta factor is one simultaneous one-step chip.
Every geometric alpha factor is expanded into `N` adjacent chips, visited from left to right.
Thus a path crossing one alpha layer from wire `i` to wire `j` is unique and has weight
`alpha^(j-i)`.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

/-- Number of elementary stages in the finite factor network. -/
def finiteFactorStageCount (p q N : ℕ) : ℕ :=
  q + p * N

/-- An allowed transition through one elementary stage. -/
def NetworkStepAllowed (p q N t : ℕ) (x y : Fin (N + 1)) : Prop :=
  if t < q then
    y.val = x.val ∨ y.val = x.val + 1
  else
    let u := t - q
    y.val = x.val ∨
      (u / N < p ∧ x.val = u % N ∧ y.val = x.val + 1)

noncomputable instance (p q N t : ℕ) (x y : Fin (N + 1)) :
    Decidable (NetworkStepAllowed p q N t x y) := Classical.dec _

/-- Weight of one elementary transition; disallowed transitions have weight zero. -/
def FiniteEdreiData.networkStepWeight {p q : ℕ} (D : FiniteEdreiData p q)
    (N t : ℕ) (x y : Fin (N + 1)) : ℝ :=
  if y.val = x.val then 1
  else if ht : t < q then
    if y.val = x.val + 1 then D.beta ⟨t, ht⟩ else 0
  else
    let u := t - q
    if ha : u / N < p then
      if x.val = u % N ∧ y.val = x.val + 1 then D.alpha ⟨u / N, ha⟩ else 0
    else
      0

/-- A path between two wires in the complete layered network. -/
structure FiniteFactorPath {p q : ℕ} (D : FiniteEdreiData p q)
    (N : ℕ) (source sink : Fin (N + 1)) where
  position : Fin (finiteFactorStageCount p q N + 1) → Fin (N + 1)
  source_eq : position 0 = source
  sink_eq : position (Fin.last (finiteFactorStageCount p q N)) = sink
  valid : ∀ t : Fin (finiteFactorStageCount p q N),
    NetworkStepAllowed p q N t.val (position t.castSucc) (position t.succ)

namespace FiniteFactorPath

theorem position_injective {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} :
    Function.Injective
      (fun P : FiniteFactorPath D N source sink ↦ P.position) := by
  intro P Q h
  cases P with
  | mk pp hs ht hv =>
    cases Q with
    | mk qp qs qt qv =>
      dsimp at h
      subst qp
      rfl

instance {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} :
    Finite (FiniteFactorPath D N source sink) :=
  Finite.of_injective (fun P ↦ P.position) position_injective

noncomputable instance {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} :
    Fintype (FiniteFactorPath D N source sink) := Fintype.ofFinite _

/-- Product of all elementary edge weights along a path. -/
def weight {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) : ℝ :=
  ∏ t : Fin (finiteFactorStageCount p q N),
    FiniteEdreiData.networkStepWeight D N t.val
      (P.position t.castSucc) (P.position t.succ)

/-- Every edge used by a valid path has strictly positive weight. -/
theorem stepWeight_pos {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink)
    (t : Fin (finiteFactorStageCount p q N)) :
    0 < FiniteEdreiData.networkStepWeight D N t.val
      (P.position t.castSucc) (P.position t.succ) := by
  have hv := P.valid t
  unfold NetworkStepAllowed at hv
  unfold FiniteEdreiData.networkStepWeight
  by_cases heq : (P.position t.succ).val = (P.position t.castSucc).val
  · simp [heq]
  · rw [if_neg heq]
    split at hv <;> rename_i ht
    · rcases hv with hv | hv
      · exact False.elim (heq hv)
      · simp [ht, hv, D.beta_pos]
    · rcases hv with hv | ⟨ha, hx, hy⟩
      · exact False.elim (heq hv)
      · simp [ht, ha, hx, hy, D.alpha_pos]

/-- Every path has strictly positive monomial weight. -/
theorem weight_pos {p q N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin (N + 1)} (P : FiniteFactorPath D N source sink) :
    0 < P.weight := by
  unfold weight
  exact Finset.prod_pos fun t _ ↦ P.stepWeight_pos t

/-- Sum of all path weights between two wires. -/
noncomputable def pathSum {p q : ℕ} (D : FiniteEdreiData p q)
    (N : ℕ) (source sink : Fin (N + 1)) : ℝ :=
  ∑ P : FiniteFactorPath D N source sink, P.weight

end FiniteFactorPath

end ToeplitzPositroids.Edrei
