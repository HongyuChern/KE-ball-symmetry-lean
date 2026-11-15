# Final manuscript and Lean correspondence

The manuscript is [`chen-KE-Ball-Symmetry-2026.tex`](../paper/chen-KE-Ball-Symmetry-2026.tex), with SHA-256 `1f8dad706f1513883619f2b4d03c48364b26dbdff7f2ca619097222910469d81`.

Section 3 presents the conclusions of [`KEBall.LogarithmicFluxStatement`](../KEBall/Specification.lean#L95) in two propositions. Its proof is used by [`KEBall.Paper20261016.currentPaper`](../KEBall/PaperFormalization20261016.lean#L36).

| Final manuscript | Component of the Lean statement |
| --- | --- |
| Proposition 3.1 (1) | The auxiliary function `auxiliaryP u` is greater than one on the closed unit ball. |
| Proposition 3.1 (2) | The metric Laplacian of `auxiliaryW u` is nonnegative on the open unit ball. |
| Proposition 3.1 (3) | Vanishing of the determinant-weighted integral implies the stated `covariantHessian20` identity. |
| Proposition 3.2 | The determinant-weighted integral equals the boundary flux with the two terms in the manuscript. |

The Lean boundary variable is `boundarySlope u = uν / 2`. Its horizontal gradient carries the same factor of one half, so the Lean coefficient of one quarter corresponds to one sixteenth in Proposition 3.2. The weight `horizontalFluxWeight n t = t^(n - 1) / t^2` also gives the reciprocal power at dimension two.

Theorem 1.1 and Corollaries 1.2 and 1.3 use the [same verified solution entry points](../KEBallComparator/Solution.lean).
