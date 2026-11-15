# Radial symmetry for the positive Kähler–Einstein Dirichlet problem on the ball

Lean 4 formalization of the [final manuscript](paper/chen-KE-Ball-Symmetry-2026.tex) by Hongyu Chen and Li Ma. The development classifies the smooth positive Kähler–Einstein Dirichlet solutions on the complex unit ball and formalizes the sharp Moser–Trudinger inequality on the Cegrell finite-energy class.

| Result | Lean entry point |
| --- | --- |
| Theorem 1.1, Corollary 1.2 and the smooth proof assembly | [`smoothPaper`](KEBallComparator/Solution.lean#L14) |
| Positive roots and the critical parameter | [`positiveRoots`](KEBallComparator/Solution.lean#L17) |
| Smooth Bedford–Taylor measure compatibility | [`smoothCompatibility`](KEBallComparator/Solution.lean#L25) |
| Subcritical attainment on the Cegrell class | [`subcriticalAttainment`](KEBallComparator/Solution.lean#L34) |
| Corollary 1.3, finite exponential integral and critical inequality | [`criticalInequality`](KEBallComparator/Solution.lean#L39) |
| Sharp energy coefficient and additive constant | [`optimalEnergyCoefficient`](KEBallComparator/Solution.lean#L28) and [`optimalAdditiveConstant`](KEBallComparator/Solution.lean#L31) |

The [statements](KEBallComparator/Statements.lean) fix the propositions checked by the [Comparator challenge](KEBallComparator/Challenge.lean). The [solution module](KEBallComparator/Solution.lean) provides the corresponding proofs. The [manuscript correspondence](docs/manuscript-correspondence.md) maps the two Section 3 propositions to their shared Lean statement.

## Build

Use Lean 4.33.1 with the dependency revisions in [lake-manifest.json](lake-manifest.json). Run the following commands from the repository root.

```sh
lake exe cache get
lake build +KEBallComparator.Solution
```

The cache command is optional. See the [Comparator instructions](KEBallComparator/README.md) for the Linux release check and for validating a saved receipt.

## Dependencies

The project pins Mathlib, PoincaréConjecture and PshLines through Lake. The bundled De Giorgi and Schauder sources retain their [license](vendor/de_giorgi/LICENSE) and [upstream notice](vendor/de_giorgi/UPSTREAM-NOTICE). Their file-level provenance is recorded in [vendor/de_giorgi](vendor/de_giorgi).

## Verification

All seven targets passed the Linux release configuration with both the Lean and Nanoda kernels. The [receipt](verification/receipt.json) records the configuration, exact input hashes, locked revisions, and kernel results. The [Comparator log](verification/comparator.log), [tool build log](verification/build.log), and [environment record](verification/environment.txt) accompany it.

Run the following command to check that the saved evidence matches this source tree.

```sh
python3 tools/run_comparator.py --verify-receipt verification/receipt.json
```

## License

The original formalization code and repository tools use [Apache-2.0](LICENSE). Third-party material retains its [source attributions and licenses](THIRD_PARTY.md). The rights holders retain their rights in the [manuscript](paper/chen-KE-Ball-Symmetry-2026.tex).
