# v0.1.0 — Initial verified release

This release accompanies Hongyu Chen and Li Ma’s final manuscript, *Radial symmetry for the positive Kähler–Einstein Dirichlet problem on the ball*. The manuscript source is [`chen-KE-Ball-Symmetry-2026.tex`](paper/chen-KE-Ball-Symmetry-2026.tex).

- Formalizes radial symmetry and the classification of smooth positive Kähler–Einstein Dirichlet solutions, including the two-solution, one-solution, and no-solution regimes.
- Formalizes subcritical mean-field classification, Bedford–Taylor compatibility for smooth potentials, and subcritical attainment on the Cegrell finite-energy class.
- Proves the critical Moser–Trudinger inequality on that class, including finiteness of the exponential integral and sharpness of both constants.

All seven [Comparator targets](KEBallComparator/Solution.lean) passed both the Lean and Nanoda kernels on Linux using Lean 4.33.1 and the locked dependencies. The release includes the [verification receipt and logs](verification/README.md).

The [manuscript correspondence](docs/manuscript-correspondence.md) maps Propositions 3.1 and 3.2 to their shared Lean statement. The formalization code uses Apache-2.0. The repository preserves [third-party credits and notices](THIRD_PARTY.md).
