import ToeplitzPositroids.Edrei.FiniteFactorNetwork
import ToeplitzPositroids.Edrei.SkewTableauLGV
import Mathlib.Data.Fintype.Sigma
import Mathlib.GroupTheory.Perm.Sign

/-!
# Leibniz path terms for the finite-factor network

The determinant expansion chooses a sink-indexed path family and a permutation of its sources.
Bad terms are precisely families with a collision at a common network stage.  The finite collision
set below gives the canonical first intersection used by the tail-swap involution.
-/

namespace ToeplitzPositroids.Edrei

open ToeplitzPositroids

/-- A determinant term: permutation of sources together with one path to every ordered sink. -/
abbrev FiniteFactorNetworkTerm {p q r N : ℕ} (D : FiniteEdreiData p q)
    (source sink : Fin r → Fin (N + 1)) :=
  Σ σ : Equiv.Perm (Fin r),
    ∀ b : Fin r, FiniteFactorPath D N (source (σ b)) (sink b)

noncomputable instance {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)} :
    Fintype (FiniteFactorNetworkTerm D source sink) := inferInstance

/-- Two paths in a term collide when they occupy the same wire at the same stage vertex. -/
def NetworkPathsCollideAt {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink)
    (b c : Fin r) (s : Fin (finiteFactorStageCount p q N + 1)) : Prop :=
  (T.2 b).position s = (T.2 c).position s

noncomputable instance {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) (b c : Fin r)
    (s : Fin (finiteFactorStageCount p q N + 1)) :
    Decidable (NetworkPathsCollideAt T b c s) := Classical.dec _

/-- A good LGV term has pairwise vertex-disjoint paths. -/
def NetworkTermGood {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) : Prop :=
  ∀ (b c : Fin r), b < c →
    ∀ s : Fin (finiteFactorStageCount p q N + 1), ¬NetworkPathsCollideAt T b c s

noncomputable instance {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) : Decidable (NetworkTermGood T) :=
  Classical.dec _

/-- Signed product of the individual path weights. -/
def networkTermSignedWeight {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) : ℝ :=
  (T.1.sign : ℤ) * ∏ b : Fin r, (T.2 b).weight

/-- All ordered collision witnesses of a bad term. -/
noncomputable def networkCollisionSet {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) :
    Finset (Fin (finiteFactorStageCount p q N + 1) × Fin r × Fin r) :=
  Finset.univ.filter fun z ↦ z.2.1 < z.2.2 ∧
    NetworkPathsCollideAt T z.2.1 z.2.2 z.1

@[simp]
theorem mem_networkCollisionSet_iff
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    {T : FiniteFactorNetworkTerm D source sink}
    {z : Fin (finiteFactorStageCount p q N + 1) × Fin r × Fin r} :
    z ∈ networkCollisionSet T ↔ z.2.1 < z.2.2 ∧
      NetworkPathsCollideAt T z.2.1 z.2.2 z.1 := by
  simp [networkCollisionSet]

/-- A term is bad exactly when its collision set is nonempty. -/
theorem networkCollisionSet_nonempty_iff_not_good
    {p q r N : ℕ} {D : FiniteEdreiData p q}
    {source sink : Fin r → Fin (N + 1)}
    (T : FiniteFactorNetworkTerm D source sink) :
    (networkCollisionSet T).Nonempty ↔ ¬NetworkTermGood T := by
  classical
  rw [Finset.nonempty_iff_ne_empty]
  simp only [NetworkTermGood, not_forall, not_not]
  constructor
  · intro hne
    obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    exact ⟨z.2.1, z.2.2, (mem_networkCollisionSet_iff.mp hz).1,
      z.1, (mem_networkCollisionSet_iff.mp hz).2⟩
  · rintro ⟨b, c, hbc, s, hcollide⟩ hempty
    have : (s, b, c) ∈ networkCollisionSet T :=
      mem_networkCollisionSet_iff.mpr ⟨hbc, hcollide⟩
    rw [hempty] at this
    simp at this

end ToeplitzPositroids.Edrei
