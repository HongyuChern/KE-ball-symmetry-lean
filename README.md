# Kähler–Einstein Dirichlet symmetry on the ball in Lean

This repository contains the Lean 4 formalization of *Radial symmetry for the positive Kähler–Einstein Dirichlet problem on the ball* by Hongyu Chen and Li Ma. The source is the [final manuscript](paper/chen-KE-Ball-Symmetry-2026.tex).

`import KEBallComparator.Solution` exposes the seven verification targets, including the [smooth-paper assembly](KEBall/PaperFormalization20261016.lean#L36). The main results are listed below. The [manuscript correspondence](docs/manuscript-correspondence.md) maps Propositions 3.1 and 3.2 to their Lean statement.

| Paper | Lean declaration | Result | Proof |
| --- | --- | --- | --- |
| Theorem 1.1 | `KEBall.Stage09.classification_and_counts` | Radial classification of smooth positive Dirichlet solutions and the two, one, or zero solution counts | [Classification and counts](Drafts/KEBall/ClassificationEndpoints.lean#L47) |
| Corollary 1.2 | `KEBall.Paper20261016.meanFieldClassification` | Existence and uniqueness of smooth mean-field solutions exactly in the subcritical range | [Mean-field classification](KEBall/PaperBridges20261016.lean#L50) |
| Corollary 1.3 | `KEBallComparator.Targets.criticalInequality` | Sharp Moser–Trudinger inequality and finite exponential integral on the Cegrell finite-energy class | [Critical inequality](KEBallComparator/Solution.lean#L39) |
| Corollary 1.3 (optimal constants) | `KEBallComparator.Targets.optimalEnergyCoefficient`, `KEBallComparator.Targets.optimalAdditiveConstant` | Optimal energy coefficient and optimal harmonic-number additive constant | [Energy coefficient](KEBall/MoserTrudingerFiniteEnergy.lean#L123) · [Additive constant](KEBall/MoserTrudingerFiniteEnergy.lean#L107) |

The critical inequality follows from [subcritical attainment on the full finite-energy class](KEBall/MoserTrudingerSubcriticalAttainment.lean#L20) by passage to the critical parameter.

## Build

Install [Elan](https://github.com/leanprover/elan) and run the commands below in the repository root. The toolchain is Lean 4.33.1, with Mathlib at revision `0df444a360eaa60ab8c11dca51a86af692955474`. [Lake's lock file](lake-manifest.json) lists the remaining dependencies.

```sh
lake exe cache get
lake build +KEBallComparator.Solution
```

The v0.1.1 source release contains **205,287 lines of Lean**. The complete import closure of `KEBallComparator.Solution` contains **1,995,054 lines of Lean**, including Mathlib, the Lean toolchain, and other dependencies.

## Comparator

The challenge states seven verification targets using the shared project definitions. Its proof placeholders are filled by the solution. The Linux run under Landrun and a systemd user service passed all seven targets in Lean and Nanoda. The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.

[Challenge](KEBallComparator/Challenge.lean) · [Statements](KEBallComparator/Statements.lean) · [Solution](KEBallComparator/Solution.lean) · [Configuration](KEBallComparator/config.json) · [Linux verification receipt](verification/receipt.json) · [Reproduction instructions](KEBallComparator/README.md)

## Source and attribution

[KEBall/](KEBall/) contains the main proof library. [Drafts/](Drafts/) and [KEBallProbe/](KEBallProbe/) supply supporting modules used by the formalization. [verification/](verification/) collects the runner, validation files, and proof-checking evidence.

The bundled De Giorgi and Schauder code supplies elliptic regularity estimates. The matrix determinant proof adapts PoincareLib's Jacobi formula to complex matrices. [Jacobi formula implementation](KEBallProbe/ComplexDeterminant.lean) · [Upstream sources, credits, and licenses](docs/THIRD_PARTY.md)

The original formalization code and verification tools use [Apache-2.0](LICENSE). The rights holders retain their rights in the manuscript.
