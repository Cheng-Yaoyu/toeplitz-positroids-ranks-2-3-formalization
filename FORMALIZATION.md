# Formalization status

This project formalizes *Toeplitz Positroids in Ranks Two and Three* in Lean 4.
The source paper is `paper/toeplitz_positroids_ranks_2_3_third_revised.tex`; theorem
names in the Lean development retain the paper's descriptive labels whenever
possible.

## Reproducible environment

- Lean: `v4.29.0`
- mathlib: `v4.29.0`
- No theorem may rely on `sorry`, `admit`, `axiom`, or an unchecked external
  computation.

## Theorem crosswalk

| Paper material | Lean module |
| --- | --- |
| Ordered minors, total nonnegativity, Toeplitz matrices | `Matrix.Basic`, `Matrix.Toeplitz`, `Matrix.Reversal` |
| Column matroids and positroid representations | `Matrix.ColumnMatroid`, `Matrix.Positroid` |
| Proposition 2 | `ToeplitzPositroids.Matrix.CornerObstruction` |
| Theorem 3 | `RankTwo.Classification`, `RankTwo.BoundaryRealization`, `RankTwo.MatroidClassification` |
| Corrected Corollary 4 and literal counterexample | `RankTwo.PositiveCorollary`, `RankTwo.Basic` |
| Lemma 5 | `RankThree.OrderTwo`, `RankThree.OrderTwoEquality` |
| Remark 6 | `RankThree.ConsecutiveCounterexample` |
| Lemma 7 | `RankThree.Moments`, `RankThree.MomentMatrix` |
| Theorem 8 | `Geometry.ConvexChain`, `RankThree.Simplification`, `RankThree.ConvexChainCriterion` |
| Theorem 10 and Lemma 11 | `ToeplitzPositroids.RankThree.EndpointParallel` |
| Definition 12 | `RankThree.CompatibleData` |
| Theorem 13 necessity, realization, and uniqueness | `RankThree.Classification`, `RankThree.ClassificationNecessity`, `RankThree.SupportUniqueness`, `RankThree.ClassificationUniqueness` |
| Lemmas 14--16 and Proposition 17 | `RankThree.SlopeSynthesis`, `RankThree.OneSided*`, `RankThree.PropositionSeventeen`, `RankThree.ReversedCompatibleData` |
| Lemma 18 | `RankThree.SineSequence`, `RankThree.SineBase` |
| Theorem 19 | `RankThree.Jacobian` |
| Theorem 20 | `RankThree.SinePerturbation`, `RankThree.ArbitraryZeroPattern` |
| Proposition 21 | `RankThree.TwoSidedCombinatorics`, `RankThree.TwoSidedRealization` |
| Theorem 23 | `Edrei.FormalSeries`, `Edrei.ToeplitzMinor`, `Edrei.FiniteFactor*`, `Edrei.FactorialKernel*`, `Edrei.EdreiCauchyBinet`, `Edrei.GammaPositiveSupport`, `Edrei.FiniteFactorNetworkWeights`, `Edrei.BetaNetwork`, `Edrei.AlphaNetwork`, `Edrei.SkewTableauBounds`, `Edrei.TableauSupport`, `Edrei.NetworkSupport` |
| Corollary 24 | `Edrei.SchubertCondition`, `Edrei.Support`, `Edrei.GammaZeroSupport`, `Edrei.PositroidCorollary` |

## Paper-level theorem API

The final classification and positroid statements are available without asking a
downstream user to assemble intermediate bridges.

- `hasTNNRankTwoToeplitzRepresentation_iff_hasCompatibleRankTwoSupport` is the
  genuine matroid-level form of Theorem 3.
- `hasTNNRankThreeToeplitzRepresentation_iff_hasCompatibleRankThreeSupport` is
  the genuine matroid-level form of Theorems 1 and 13.
- `HasTNNRankThreeToeplitzRepresentation.existsUnique_compatibleSupportSignature`
  states the proof-irrelevant uniqueness of the compatible loop, parallel-pair,
  and maximal rank-two-flat collection with `∃!`.
- `FiniteEdreiData.firstRowBlockPositroidRepresentation` bundles the first-row
  block as an actual positroid representation. The theorems
  `firstRowBlockPositroid_hasSchubertBasisSupport_of_gamma_zero` and
  `firstRowBlockPositroid_hasUniformBasisSupport_of_gamma_pos`, together with
  the two zero-gamma uniform specializations, give Corollary 24 directly for its
  column matroid. The theorem `FiniteEdreiData.corollaryTwentyFour` packages all
  of these conclusions in one paper-level statement.

## Clarifications made explicit by formalization

The following points are implicit or informal in the manuscript and will be
stated with full quantifiers in Lean.

1. Endpoint slope synthesis includes the required smallness bounds on its
   starting ratios.
2. Coefficient translations inserting prefix and suffix loop blocks are explicit
   functions, with index-preservation lemmas.
3. In the two-sided realization, the band parameter is explicitly related to the
   simplified ground-set size by `d = m - 3`.
4. The arbitrary-zero-pattern theorem includes a quantified neighborhood and a
   proof of the stated "arbitrarily close" conclusion.
5. The auxiliary weakly increasing slope sequence is constructed from the
   compatible interval family rather than merely chosen.
6. The finite Edrei section is treated as an independent dependency branch,
   including every symmetric-function result needed by the support theorem.

## Correctness findings

The low-rank audit found one missing hypothesis in the manuscript. Corollary 4,
read literally, assumes only that the entries of a rank-two Toeplitz matrix are
positive. This is insufficient: the coefficient tuple
`(a₋₁, a₀, a₁, a₂) = (1, 1, 2, 2)` gives the positive rank-two matrix

```text
1 2 2
1 1 2
```

whose first and third columns are parallel, so its parallel class is not a
consecutive interval. The intended corollary follows from Theorem 3 after adding
the standing total-nonnegativity hypothesis. The corrected Lean theorem is
`positive_rankTwoToeplitz_parallelClasses_form_composition`, and the literal
counterexample is formalized in `ToeplitzPositroids.RankTwo.Basic`. The stronger
theorem `literal_corollary_four_fails_for_genuine_positroid` proves that its
column matroid is nevertheless equal to one represented by a matrix with all
ordered maximal minors nonnegative.

## Current Section 10 status

The finite Edrei/network branch is now fully formalized without placeholders.
Transfer matrices, finite-factor path sums, Cauchy--Binet truncation,
sign-reversing LGV cancellation, the path-to-tableau map, and its unconditional
weight identity all compile in Lean.  The converse construction is complete in
all parameter regimes: `Edrei.TableauBetaBijection` handles `p = 0`,
`Edrei.TableauAlphaSplice` handles `p > 0, q = 0`, and
`Edrei.TableauMixedSplice` handles `p > 0, q > 0`, including the degenerate
tuple-width-zero case.

In the mixed module, Lean checks the boundary-spliced paths, every network step,
cross-boundary vertex-disjointness, the intermediate partition, and exact
beta/alpha crossing-stage and entry reconstruction.  It proves
`canonicalGoodTableauMap_bijective_mixed_positiveWidth` and the zero-width
variant, combines them into `canonicalGoodBijectionBridge_mixed`, and derives
`finiteFactorMinor_eq_tupleCoproductWeight_sum_mixed` and
`finiteFactorMinor_pos_iff_indexHook_mixed`.

The parameter cases are unified by `canonicalGoodBijectionBridge_gamma_zero`,
`finiteFactorMinor_eq_tupleCoproductWeight_sum_gamma_zero`, and
`finiteFactorMinor_pos_iff_indexHook_gamma_zero`.
`Edrei.GammaZeroSupport` instantiates this bridge in the Toeplitz-minor support
criterion. `Edrei.PositroidCorollary` additionally proves total nonnegativity and
full row rank of every finite first-row block, bundles its column matroid, and
states the Schubert and uniform conclusions without an abstract bridge argument.

The repository-wide check is `lake build` (3446 targets).  A source search
confirms that no Lean file contains `sorry`, `admit`, or `axiom`.
