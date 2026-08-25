import ToeplitzPositroids.RankThree.Classification

/-!
# Explicit uniqueness form of the rank-three classification

The paper's compatible collection consists of its loop set, endpoint-parallel relation, and
maximal rank-two-flat family.  `Classification.lean` proves equality of these three components.
This file packages them as one support signature and states the resulting literal uniqueness
theorem with `∃!`.
-/

namespace ToeplitzPositroids

noncomputable section

/-- The proof-irrelevant combinatorial content of compatible rank-three Toeplitz data. -/
structure RankThreeSupportSignature (n : ℕ) where
  loops : Finset (Fin n)
  parallelPairs : Finset (Fin n × Fin n)
  rankTwoFlats : Finset (Finset (Fin n))

@[ext]
theorem RankThreeSupportSignature.ext {n : ℕ} {S T : RankThreeSupportSignature n}
    (hloops : S.loops = T.loops)
    (hparallel : S.parallelPairs = T.parallelPairs)
    (hflats : S.rankTwoFlats = T.rankTwoFlats) : S = T := by
  cases S
  cases T
  simp_all

namespace CompatibleRankThreeData

variable {n : ℕ}

/-- Forget the numeric encoding and proof fields, retaining exactly the compatible collection
recovered from basis support. -/
def supportSignature (D : CompatibleRankThreeData n) : RankThreeSupportSignature n where
  loops := D.supportLoops
  parallelPairs := D.supportParallelPairs
  rankTwoFlats := D.supportRankTwoFlats

/-- Two compatible data sets realizing the same rank-three matroid have equal support
signatures. -/
theorem supportSignature_eq_of_compatibleTripleSupportRealizations
    {D E : CompatibleRankThreeData n} {M : Matroid (Fin n)}
    (RD : CompatibleTripleSupportRealization D M)
    (RE : CompatibleTripleSupportRealization E M) :
    D.supportSignature = E.supportSignature := by
  obtain ⟨hloops, hparallel, hflats⟩ :=
    supportComponents_eq_of_compatibleTripleSupportRealizations D RD RE
  apply RankThreeSupportSignature.ext
  · exact hloops
  · exact hparallel
  · exact hflats

end CompatibleRankThreeData

/-- Literal uniqueness of the compatible collection, expressed in its proof-irrelevant support
signature. -/
theorem HasCompatibleRankThreeSupport.existsUnique_supportSignature
    {n : ℕ} {M : Matroid (Fin n)} (hM : HasCompatibleRankThreeSupport M) :
    ∃! S : RankThreeSupportSignature n,
      ∃ D : CompatibleRankThreeData n,
        CompatibleTripleSupportRealization D M ∧ D.supportSignature = S := by
  obtain ⟨D, RD⟩ := hM
  refine ⟨D.supportSignature, ⟨D, RD, rfl⟩, ?_⟩
  intro S hS
  obtain ⟨E, RE, rfl⟩ := hS
  exact (CompatibleRankThreeData.supportSignature_eq_of_compatibleTripleSupportRealizations
    RD RE).symm

/-- The exact rank-three cell list with the paper's uniqueness conclusion made explicit. -/
theorem HasTNNRankThreeToeplitzRepresentation.existsUnique_compatibleSupportSignature
    {n : ℕ} {M : Matroid (Fin n)} (hM : HasTNNRankThreeToeplitzRepresentation M) :
    ∃! S : RankThreeSupportSignature n,
      ∃ D : CompatibleRankThreeData n,
        CompatibleTripleSupportRealization D M ∧ D.supportSignature = S :=
  HasCompatibleRankThreeSupport.existsUnique_supportSignature
    (hasCompatibleRankThreeSupport_of_hasTNNRankThreeToeplitzRepresentation hM)

end

end ToeplitzPositroids
