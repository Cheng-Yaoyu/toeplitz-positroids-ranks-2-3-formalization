# Toeplitz Positroids in Ranks Two and Three

Lean 4 formalization of *Toeplitz Positroids in Ranks Two and Three*.

This repository is **Paper A** in the Toeplitz-positroid project. It gives the
complete rank-two and rank-three classification, including loops, endpoint
parallel classes, lower-rank interval flats, and the finite-Edrei support
formula. The arbitrary-rank paving sector is treated separately in **Paper B**:
[`Cheng-Yaoyu/paving-toeplitz-positroids-formalization`](https://github.com/Cheng-Yaoyu/paving-toeplitz-positroids-formalization).

## Paper

The corrected fourth revision is available as
[`paper/toeplitz_positroids_ranks_2_3_fourth_revised.pdf`](paper/toeplitz_positroids_ranks_2_3_fourth_revised.pdf),
with its LaTeX source in the same directory.  It makes the standing
total-nonnegativity hypothesis explicit in Corollary 4, records the positive
Toeplitz counterexample showing that entrywise positivity alone is insufficient,
and incorporates the terminology, quantifier, and bibliography clarifications
from the subsequent independent assessment.

The project is pinned to Lean and mathlib `v4.29.0`. Build the checked library
with:

```sh
lake build
```

See `FORMALIZATION.md` for the theorem crosswalk, explicit clarifications made
during formalization, and correctness findings.  The zero-gamma Edrei
tableau/network bridge is fully checked: `Edrei.NetworkTableauBridge` constructs
crossing-stage tableaux, `Edrei.NetworkTableauWeightBridge` proves the
unconditional weight identity, and `Edrei.NetworkTableauConcreteBridge` packages
the canonical map.

The paper-level conclusions are also exposed directly at their natural semantic
level. `RankTwo.MatroidClassification` states Theorem 3 as an equivalence for
genuine column matroids, `RankThree.ClassificationUniqueness` packages the unique
compatible support signature with `∃!`, and `Edrei.PositroidCorollary` bundles the
finite first-row block as a `PositroidRepresentation` and proves the Schubert and
uniform conclusions of Corollary 24 for its actual column matroid.

The converse map is complete in every parameter regime.  The beta-only case is
handled by `Edrei.TableauBetaPath`, which constructs the inverse paths and proves their
vertex-disjointness, while `Edrei.TableauBetaBijection` proves the inverse laws,
the canonical bijection for `p = 0`, the exact tableau expansion, and the finite
hook support criterion. `Edrei.TableauAlphaPath` contains the checked
row-level block counts, prefix bounds, and local alpha-block path positions;
`Edrei.TableauAlphaSplice` now splices all alpha blocks in the `q = 0` slice,
proves row-path validity and endpoints, and proves injectivity of the canonical
tableau map for arbitrary `p > 0`. It also proves global strict row ordering of
all spliced path positions, hence vertex-disjointness, identifies the
intermediate partition, and verifies every reconstructed alpha crossing stage
and entry. The canonical map is therefore bijective in the full `q = 0` slice,
with the exact finite-factor expansion
`finiteFactorMinor_eq_tupleCoproductWeight_sum_p_pos_q_zero`.
The q-zero slices are also unified in the expansion and support theorems
`finiteFactorMinor_eq_tupleCoproductWeight_sum_q_zero` and
`finiteFactorMinor_pos_iff_indexHook_q_zero`.
`Edrei.TableauMixedSplice` now formalizes the entire mixed construction for
`p > 0`, `q > 0`: boundary-spliced paths, legal network steps, endpoints,
cross-boundary noncollision, the intermediate partition, exact crossing-stage
and entry reconstruction, and canonical-map bijectivity.  It handles both
positive tuple width and the degenerate width-zero case, and derives
`finiteFactorMinor_eq_tupleCoproductWeight_sum_mixed` together with
`finiteFactorMinor_pos_iff_indexHook_mixed`.
`Edrei.GammaZeroSupport` then instantiates the unified bridge in the Toeplitz-minor
support criterion.
`Edrei.TableauAlphaBijection` additionally proves deterministic path uniqueness
and canonical-map bijectivity for the one-alpha/no-beta network slice, including
the exact finite-factor tableau expansion.
