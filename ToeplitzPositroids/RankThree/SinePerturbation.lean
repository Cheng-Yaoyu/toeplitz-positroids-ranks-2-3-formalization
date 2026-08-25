import ToeplitzPositroids.RankThree.Jacobian
import ToeplitzPositroids.RankThree.SineBase
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

/-!
# Open perturbations of the sine base point

This file supplies the topological part of the perturbation argument used in
Theorem 20.  It is independent of the invertibility calculation for the
Jacobian: positivity and strict zero-boundary log-concavity are packaged as an
open source neighborhood of the sine interior point.  We also construct small
nonnegative target vectors with any prescribed zero pattern.
-/

namespace ToeplitzPositroids.RankThree

open Filter Set Topology

noncomputable section

variable {d : ℕ}

/-- At the sine interior point, reinserting the endpoints recovers the full sine vector. -/
theorem fixedEndpointBand_sineInterior (d : ℕ) :
    fixedEndpointBand d (sineInterior d) = sineCoefficient d := by
  funext t
  rw [fixedEndpointBand, fixedEndpointCoefficient_sineInterior]
  simp [sineExtended, sineCoefficient]

/-- Every fixed-endpoint coefficient depends continuously on the interior variables. -/
theorem continuous_fixedEndpointCoefficient (d : ℕ) (k : ℤ) :
    Continuous (fun x : Fin (d - 1) → ℝ ↦ fixedEndpointCoefficient d x k) := by
  unfold fixedEndpointCoefficient
  split_ifs
  · exact continuous_apply _
  · exact continuous_const

/-- Every displayed coordinate of the reassembled band is continuous. -/
theorem continuous_fixedEndpointBand_apply (d : ℕ) (t : Fin (d + 1)) :
    Continuous (fun x : Fin (d - 1) → ℝ ↦ fixedEndpointBand d x t) := by
  exact continuous_fixedEndpointCoefficient d t

/-- Every zero-extended band coefficient remains a continuous function of the
interior variables. -/
theorem continuous_bandCoefficient_fixedEndpointBand (d : ℕ) (k : ℤ) :
    Continuous (fun x : Fin (d - 1) → ℝ ↦ bandCoefficient (fixedEndpointBand d x) k) := by
  unfold bandCoefficient
  split_ifs
  · exact continuous_fixedEndpointBand_apply d _
  · exact continuous_const

/-- Interior points whose reassembled coefficients are positive and strictly
log-concave with the zero-boundary convention. -/
def sineAdmissibleSet (d : ℕ) : Set (Fin (d - 1) → ℝ) :=
  {x | StrictlyLogConcaveWithZeroBoundary (fixedEndpointBand d x)}

/-- Positivity and strict zero-boundary log-concavity define an open set in the
finite-dimensional interior coefficient space. -/
theorem isOpen_sineAdmissibleSet (d : ℕ) : IsOpen (sineAdmissibleSet d) := by
  change IsOpen
    ({x | ∀ t, 0 < fixedEndpointBand d x t} ∩
      {x | ∀ t : Fin (d + 1),
        bandCoefficient (fixedEndpointBand d x) (t - 1) *
            bandCoefficient (fixedEndpointBand d x) (t + 1) <
          fixedEndpointBand d x t ^ 2})
  apply IsOpen.inter
  · rw [show {x | ∀ t, 0 < fixedEndpointBand d x t} =
        ⋂ t, {x | 0 < fixedEndpointBand d x t} by ext x; simp]
    apply isOpen_iInter_of_finite
    intro t
    exact isOpen_lt continuous_const (continuous_fixedEndpointBand_apply d t)
  · rw [show {x | ∀ t : Fin (d + 1),
        bandCoefficient (fixedEndpointBand d x) (t - 1) *
            bandCoefficient (fixedEndpointBand d x) (t + 1) <
          fixedEndpointBand d x t ^ 2} =
      ⋂ t : Fin (d + 1),
        {x | bandCoefficient (fixedEndpointBand d x) (t - 1) *
            bandCoefficient (fixedEndpointBand d x) (t + 1) <
          fixedEndpointBand d x t ^ 2} by ext x; simp]
    apply isOpen_iInter_of_finite
    intro t
    exact isOpen_lt
      ((continuous_bandCoefficient_fixedEndpointBand d (t - 1)).mul
        (continuous_bandCoefficient_fixedEndpointBand d (t + 1)))
      ((continuous_fixedEndpointBand_apply d t).pow 2)

/-- The sine interior point belongs to the admissible open set. -/
theorem sineInterior_mem_admissible (d : ℕ) : sineInterior d ∈ sineAdmissibleSet d := by
  change StrictlyLogConcaveWithZeroBoundary (fixedEndpointBand d (sineInterior d))
  rw [fixedEndpointBand_sineInterior]
  exact sineStrictlyLogConcaveWithZeroBoundary d

/-- The admissible set is an open neighborhood of the sine interior point. -/
theorem sineAdmissibleSet_mem_nhds (d : ℕ) : sineAdmissibleSet d ∈ 𝓝 (sineInterior d) :=
  (isOpen_sineAdmissibleSet d).mem_nhds (sineInterior_mem_admissible d)

/-- The canonical source neighborhood inside a requested metric ball. -/
def sineSourceNeighborhood (d : ℕ) (epsilon : ℝ) : Set (Fin (d - 1) → ℝ) :=
  sineAdmissibleSet d ∩ Metric.ball (sineInterior d) epsilon

/-- The canonical source neighborhood is open. -/
theorem isOpen_sineSourceNeighborhood (d : ℕ) (epsilon : ℝ) :
    IsOpen (sineSourceNeighborhood d epsilon) :=
  (isOpen_sineAdmissibleSet d).inter Metric.isOpen_ball

/-- For positive radius, the source neighborhood contains the sine point. -/
theorem sineInterior_mem_sourceNeighborhood (d : ℕ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    sineInterior d ∈ sineSourceNeighborhood d epsilon :=
  ⟨sineInterior_mem_admissible d, Metric.mem_ball_self hepsilon⟩

/-- The source neighborhood is contained in the requested epsilon ball. -/
theorem sineSourceNeighborhood_subset_ball (d : ℕ) (epsilon : ℝ) :
    sineSourceNeighborhood d epsilon ⊆ Metric.ball (sineInterior d) epsilon :=
  inter_subset_right

/-- Every point of the source neighborhood has positive, strictly
zero-boundary-log-concave coefficients. -/
theorem sourceNeighborhood_admissible {d : ℕ} {epsilon : ℝ}
    {x : Fin (d - 1) → ℝ} (hx : x ∈ sineSourceNeighborhood d epsilon) :
    StrictlyLogConcaveWithZeroBoundary (fixedEndpointBand d x) :=
  hx.1

/-- Membership in the source neighborhood gives the requested norm bound. -/
theorem sourceNeighborhood_norm_sub_lt {d : ℕ} {epsilon : ℝ}
    {x : Fin (d - 1) → ℝ} (hx : x ∈ sineSourceNeighborhood d epsilon) :
    ‖x - sineInterior d‖ < epsilon := by
  simpa [Metric.mem_ball, dist_eq_norm] using hx.2

/-- A source neighborhood can be placed inside any requested positive epsilon
ball around the sine point. -/
theorem exists_sineSourceNeighborhood (_hd : 2 ≤ d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ U : Set (Fin (d - 1) → ℝ),
      IsOpen U ∧ sineInterior d ∈ U ∧
        U ⊆ Metric.ball (sineInterior d) epsilon ∧
        ∀ x ∈ U, StrictlyLogConcaveWithZeroBoundary (fixedEndpointBand d x) := by
  refine ⟨sineSourceNeighborhood d epsilon, isOpen_sineSourceNeighborhood d epsilon,
    sineInterior_mem_sourceNeighborhood d hepsilon,
    sineSourceNeighborhood_subset_ball d epsilon, ?_⟩
  intro x hx
  exact sourceNeighborhood_admissible hx

/-- For positive radius, the source set is a neighborhood in the filter sense. -/
theorem sineSourceNeighborhood_mem_nhds (_hd : 2 ≤ d) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    sineSourceNeighborhood d epsilon ∈ 𝓝 (sineInterior d) :=
  (isOpen_sineSourceNeighborhood d epsilon).mem_nhds
    (sineInterior_mem_sourceNeighborhood d hepsilon)

section TargetVectors

/-- The `0`/`1` target vector with zero set exactly `Z`. -/
noncomputable def targetIndicator (Z : Set (Fin (d - 1))) : Fin (d - 1) → ℝ := by
  classical
  exact fun i ↦ if i ∈ Z then 0 else 1

@[simp]
theorem targetIndicator_apply_mem {Z : Set (Fin (d - 1))} {i : Fin (d - 1)}
    (hi : i ∈ Z) : targetIndicator Z i = 0 := by
  classical
  simp [targetIndicator, hi]

@[simp]
theorem targetIndicator_apply_not_mem {Z : Set (Fin (d - 1))} {i : Fin (d - 1)}
    (hi : i ∉ Z) : targetIndicator Z i = 1 := by
  classical
  simp [targetIndicator, hi]

/-- A positive scalar multiple has precisely the requested zero coordinates. -/
theorem targetIndicator_pos_smul_eq_zero_iff {Z : Set (Fin (d - 1))}
    {r : ℝ} (hr : 0 < r) (i : Fin (d - 1)) :
    (r • targetIndicator Z) i = 0 ↔ i ∈ Z := by
  classical
  by_cases hi : i ∈ Z
  · simp [targetIndicator, hi]
  · simp [targetIndicator, hi, hr.ne']

/-- Off the prescribed zero set, every coordinate of a positive scalar multiple
is strictly positive. -/
theorem targetIndicator_pos_smul_pos_iff {Z : Set (Fin (d - 1))}
    {r : ℝ} (hr : 0 < r) (i : Fin (d - 1)) :
    0 < (r • targetIndicator Z) i ↔ i ∉ Z := by
  classical
  by_cases hi : i ∈ Z
  · simp [targetIndicator, hi]
  · simp [targetIndicator, hi, hr]

/-- Positive scalar multiples of the indicator are coordinatewise nonnegative. -/
theorem targetIndicator_pos_smul_nonneg {Z : Set (Fin (d - 1))}
    {r : ℝ} (hr : 0 < r) (i : Fin (d - 1)) :
    0 ≤ (r • targetIndicator Z) i := by
  classical
  by_cases hi : i ∈ Z <;> simp [targetIndicator, hi, hr.le]

/-- The zero set of a positive scalar multiple is exactly `Z`. -/
theorem targetIndicator_zero_set {Z : Set (Fin (d - 1))} {r : ℝ} (hr : 0 < r) :
    {i | (r • targetIndicator Z) i = 0} = Z := by
  ext i
  exact targetIndicator_pos_smul_eq_zero_iff hr i

/-- A canonical sequence of positive target vectors shrinking to zero. -/
def shrinkingTarget (Z : Set (Fin (d - 1))) (N : ℕ) : Fin (d - 1) → ℝ :=
  (1 / ((N : ℝ) + 1)) • targetIndicator Z

/-- Every scale used by `shrinkingTarget` is positive. -/
theorem shrinkingTarget_scale_pos (N : ℕ) : 0 < 1 / ((N : ℝ) + 1) := by
  positivity

/-- Every shrinking target has exactly the prescribed zero pattern. -/
theorem shrinkingTarget_eq_zero_iff {Z : Set (Fin (d - 1))} (N : ℕ)
    (i : Fin (d - 1)) :
    shrinkingTarget Z N i = 0 ↔ i ∈ Z := by
  exact targetIndicator_pos_smul_eq_zero_iff (shrinkingTarget_scale_pos N) i

/-- The nonzero coordinates of every shrinking target are positive. -/
theorem shrinkingTarget_pos_iff {Z : Set (Fin (d - 1))} (N : ℕ)
    (i : Fin (d - 1)) :
    0 < shrinkingTarget Z N i ↔ i ∉ Z := by
  exact targetIndicator_pos_smul_pos_iff (shrinkingTarget_scale_pos N) i

/-- The canonical target vectors converge to zero in the finite-dimensional
sup-norm topology. -/
theorem shrinkingTarget_tendsto_zero (Z : Set (Fin (d - 1))) :
    Tendsto (shrinkingTarget Z) atTop (𝓝 0) := by
  change Tendsto
    (fun N : ℕ ↦ (1 / ((N : ℝ) + 1)) • targetIndicator Z) atTop (𝓝 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (targetIndicator Z)

/-- Scalar multiples of the indicator depend continuously on the scalar and
therefore converge to zero whenever their scalar does. -/
theorem targetIndicator_smul_tendsto_zero (Z : Set (Fin (d - 1))) :
    Tendsto (fun r : ℝ ↦ r • targetIndicator Z) (𝓝 0) (𝓝 0) := by
  have h : ContinuousAt (fun r : ℝ ↦ r • targetIndicator Z) 0 :=
    (continuous_id.smul (continuous_const :
      Continuous fun _ : ℝ ↦ targetIndicator Z)).continuousAt
  have hz : (0 : Fin (d - 1) → ℝ) = (0 : ℝ) • targetIndicator Z := by simp
  rw [hz]
  exact h

end TargetVectors

end

end ToeplitzPositroids.RankThree
