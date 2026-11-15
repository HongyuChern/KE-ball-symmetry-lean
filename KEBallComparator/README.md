# Comparator verification

The verification target is [chen-KE-Ball-Symmetry-2026.tex](../paper/chen-KE-Ball-Symmetry-2026.tex). The selected file has SHA-256 1f8dad706f1513883619f2b4d03c48364b26dbdff7f2ca619097222910469d81.

[Statements.lean](Statements.lean) fixes the propositions. [Challenge.lean](Challenge.lean) declares the named targets using proof placeholders. [Solution.lean](Solution.lean) imports the statements and the proof library. Normal Lean builds and production proofs are independent of the challenge module.

| Target | Manuscript result |
| --- | --- |
| smoothPaper | Theorem 1.1, Corollary 1.2, the boundary identities and lower slope estimate, and the proof and normalization endpoints assembled in CurrentPaperStatement |
| positiveRoots | The positive-root lemma for the boundary polynomial and the radial parameter |
| smoothCompatibility | Identification of the smooth Bedford–Taylor and oriented top-form measures |
| subcriticalAttainment | A smooth mean-field maximizer of the subcritical functional over the actual Cegrell finite-energy class |
| criticalInequality | The finite exponential integral and critical inequality in Corollary 1.3 |
| optimalEnergyCoefficient | A finite-energy counterexample to each smaller energy coefficient for any fixed additive constant |
| optimalAdditiveConstant | The harmonic-number lower bound for every admissible additive constant at the stated energy coefficient |

## Run the release check

Use Python 3.11 or later and the Lean toolchain and dependencies in the repository's lock files. Use Linux with Landlock, a working user systemd session, and Landrun and Nanoda in PATH. The corresponding tool revisions from the reference verification are Landrun **811cfff51ceaf3d9843708aa6d22e9b84ccac8b4** and Nanoda **079049d584b2aed2b0172218164082f4fc6eede2**. [Landrun source](https://github.com/Zouuup/landrun/tree/811cfff51ceaf3d9843708aa6d22e9b84ccac8b4) · [Nanoda source](https://github.com/ammkrn/nanoda_lib) · [Reference verification](https://github.com/frenzymath/PoincareConjecture/blob/main/Comparator/README.md)

To build the reference tools from source as a regular Linux user, install Git, Go 1.24 or later, and a Rust toolchain with Cargo. Set `KE_COMPARATOR_TOOLS` to the absolute path of a new directory and run the following commands. The source checkouts and executables stay in that directory.

```sh
mkdir -p "$KE_COMPARATOR_TOOLS/bin"
git clone https://github.com/Zouuup/landrun.git "$KE_COMPARATOR_TOOLS/landrun"
git -C "$KE_COMPARATOR_TOOLS/landrun" checkout --detach 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(
  cd "$KE_COMPARATOR_TOOLS/landrun"
  go build -mod=readonly -o "$KE_COMPARATOR_TOOLS/bin/landrun" ./cmd/landrun
)
git clone https://github.com/ammkrn/nanoda_lib.git "$KE_COMPARATOR_TOOLS/nanoda"
git -C "$KE_COMPARATOR_TOOLS/nanoda" checkout --detach 079049d584b2aed2b0172218164082f4fc6eede2
cargo install --locked --path "$KE_COMPARATOR_TOOLS/nanoda" --bin nanoda_bin --root "$KE_COMPARATOR_TOOLS"
export PATH="$KE_COMPARATOR_TOOLS/bin:$PATH"
```

With both executables installed for the current Linux user, run from the repository root:

    python3 verification/run_comparator.py --output /absolute/path/to/new-ke-comparator-evidence

The runner builds the pinned Comparator and lean4export executables. Lake materializes missing dependencies from the checked-in manifest, and the runner checks all dependency revisions before invoking Comparator. Comparator runs in the user systemd service with the address-family restriction from the reference setup. It builds and exports the challenge and solution, compares the propositions, checks transitive axioms and replays the proofs in Nanoda and Lean. The only permitted axioms are propext, Classical.choice and Quot.sound.

Use a disk-backed output directory for the logs and temporary files. A successful run writes `receipt.json` with `release_verified` set to true. Keep the receipt with `comparator.log` and `build.log`. The receipt records the invocation, target list, exact Lean version, source and configuration hashes, dependency revisions, executable hashes, UTC timestamps, success markers and exit code. For a Git checkout it also records the commit and tree and whether the hashed inputs were tracked and the tracked files were clean. Run from the clean release commit to attach the evidence to that revision. A change to any covered source, dependency or recorded revision during the run invalidates the receipt.

To check the saved evidence against the same sources without running either kernel, keep the three files together and run:

    python3 verification/run_comparator.py --verify-receipt /absolute/path/to/evidence/receipt.json

This checks the files, target scope, log digests and success markers. Reproduce the kernel checks using the release command above. The published evidence for the [Poincaré formalization](https://github.com/frenzymath/Poincare-Conjecture/blob/main/archive/PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md) follows this same practice of retaining the checked revision, verifier configuration and logs.

## Check the available proofs locally

    python3 verification/run_comparator.py --preflight

The preflight configuration checks the smooth-paper assembly, positive roots, smooth compatibility and the two sharpness results. On macOS it uses Comparator's upstream development shim and the Lean default kernel. The resulting receipt records macos-development and release_verified=false. The release configuration also demands unconditional subcritical attainment and the critical inequality, and requires the dual-kernel Linux run.
