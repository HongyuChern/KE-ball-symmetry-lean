# Third-party code

## Elliptic regularity

The bundled [De Giorgi and Schauder library](../vendor/de_giorgi) comes from [DifferentialGeometry v0.1.3](https://github.com/qinz1yang/differential-geometry/tree/7a48598d35109aa99d1cc678e2724c213cdf4ff3). The De Giorgi portion builds on [the Lean development of Scott Armstrong and Julia Kempe](https://github.com/scottnarmstrong/DeGiorgi/tree/4c1b3077d3782b24065184df4ba59501b2e56fc7). The release retains the [DifferentialGeometry license](../vendor/de_giorgi/LICENSE), [upstream notice](../vendor/de_giorgi/UPSTREAM-NOTICE), and [De Giorgi license](../vendor/licenses/DeGiorgi.LICENSE). The vendor directory records pinned file hashes, provenance, and local patches. [`DirichletHolderThree.lean`](../KEBall/DirichletHolderThree.lean) and [`DirichletInterpolationDiscrete.lean`](../KEBall/DirichletInterpolationDiscrete.lean) describe their adaptations in their source headers.

## Determinant differentiation

[`KEBallProbe/ComplexDeterminant.lean`](../KEBallProbe/ComplexDeterminant.lean) adapts the multilinear and adjugate proof of Jacobi's formula in [PoincareLib at the locked revision](https://github.com/frenzymath/PoincareConjecture/blob/62db01af9388dc1d9b56b66d6674f4c09b2318a2/PoincareLib/Analysis/Matrix/Determinant.lean). That file is byte-identical to the [original Poincaré project source](https://github.com/frenzymath/Poincare-Conjecture/blob/432c38f2aa5a30efb13871292d17b4a3309a496a/PoincareConjecture/PoincareLib/Analysis/Matrix/Determinant.lean) with SHA-256 `aee0ebefe285dad65523a8e802deaf0fc35e6c0644ec0f15878eb1d48272862f`. The release includes the [upstream license](../vendor/licenses/Poincare-Conjecture.LICENSE), [upstream notice](../vendor/licenses/Poincare-Conjecture.NOTICE), and [adaptation notice](../vendor/licenses/PoincareLib.NOTICE).

## External dependencies

[Lake's lock file](../lake-manifest.json) records Mathlib, PoincareConjecture, PshLines, and the other dependencies obtained at build time. The [Comparator guide](../KEBallComparator/README.md) records the external verification tools.
