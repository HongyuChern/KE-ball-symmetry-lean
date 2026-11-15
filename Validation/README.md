# Production verification and scope

The only manuscript is `source/KE_Ball_Symmetry_20261012_v4.tex`. Its frozen SHA256, Lean version, Lean commit, Mathlib revision and Poincare revision are checked by `tools/verify_production.py`. Every transitive manifest package must also have its recorded Git revision and unchanged tracked sources.

## Commands

Run a selected, frozen dependency closure without changing the shared production objects:

```sh
python3 tools/verify_production.py --modules KEBall.Endpoints
```

Run all current production modules after the coordinator has frozen all source files:

```sh
python3 tools/verify_production.py
```

Run the complete production build and demand whole-paper acceptance:

```sh
python3 tools/verify_production.py --build --require-whole-paper
```

The build flag explicitly targets both libraries and every discovered production module. A module omitted from a top-level aggregate import therefore cannot evade the build. The script never starts a build unless `--build` is supplied. All output goes to a uniquely named immutable run directory in `logs/`.

Run the isolated failure-injection tests:

```sh
python3 tools/verify_production.py --self-test
```

The negative fixtures are generated inside their own log directory and are never imported by production code. These tests cover an unused private axiom, an admitted proof, elaboration failure, a missing import/empty audit stream, private declarations, and a conditional theorem with an extra `False` premise that must fail the exact endpoint check.

## What the source checker does

The checker replays exact source bytes under the original module names, in an isolated object directory. Its instrumented copy imports `Validation.AuditSupport` and appends one audit command. Production definitions are forbidden from depending on the instrumentation. The original production object directory is removed from the isolated Lean search path, so a missing dependency edge cannot silently load a stale local object.

The appended command enumerates every current-module kernel declaration, including private declarations, structure-generated constants, instances and generated proof helpers. It forces checked declarations, computes each recursive axiom closure with Lean's `collectAxioms`, and permits only `propext`, `Classical.choice` and `Quot.sound`. The source and instrument hashes, full elaborated types, `pp.all` definition bodies, raw type expressions and direct dependencies are retained. Theorem types are saved in full; recursive proof dependencies are audited even though theorem proof bodies are not pretty-printed in the human-facing type file.

A nonzero Lean exit code, incomplete record stream, missing checked object, record identity/count error, source mutation, type metavariable or forbidden axiom cannot be marked `PASS`. A compiler error that Lean recovers from by inserting `sorryAx` is a failure, never an empty-axiom success.

## Scope success versus whole-paper completion

Exit code 0 means the requested source-audit scope passed. It does **not** mean the whole paper is proved. With `--require-whole-paper`, a valid but incomplete scope returns exit code 3. Other audit/build/environment failures return 1. Each report explicitly includes `whole_paper` and the individual acceptance gates.

Whole-paper acceptance is computed from actual gates:

- Every current production source was replayed and its hash remained unchanged.
- The complete production build in that run succeeded.
- Actual toolchain, dependency revisions and the frozen v4 manuscript matched.
- Every required endpoint is a real proof of its independently reviewed specification, with no extra hypotheses.
- An independent final semantic report is bound by report hash and the exact complete production source map.
- A source-bound reuse report records a substantive upstream theorem on a real proved-endpoint dependency path, plus an independently reviewed consumer of a generic new declaration in another module.
- Any deployed independent checker has a real completed verification; an unrun deployed checker blocks completion.

The specification constants in `KEBall.Specification` are propositions to prove. They do not supply proofs. Null endpoint proof names are unresolved obligations. A named proof outside a selected scope is recorded `OUT_OF_SCOPE`, not credited from an old run. The endpoint command checks definitional equality of the proof's full type with the specified proposition and checks its recursive axioms again.

Registered `Validation.*` consumer modules are also replayed by the default audit and contribute their actual declarations to the dependency graph. They remain separate from production-library targets and are never imported into production proofs. Their source hashes are included in the complete reviewed source map; a missing registered consumer is an error. `Validation.RowGradientConsumer` reuses the existing non-KE vector-map Piola example exactly. `Validation.BallGreenConsumer` uses the actual nonzero-boundary vector field V(x)=x to consume the local normalized ball Green theorem.

`endpoint_contract.json` keeps final semantic/reuse fields unresolved until real review artifacts exist. No hand-written `PASS` field alone completes either gate: the referenced file hash and complete current source map must match, and registered dependency/consumer links must exist in the actual declaration graph. Mathematical noncircularity and substance of those links remain duties of the independent semantic reviewer.

## Comparator and Nanoda

The [Comparator runner](../KEBallComparator/README.md) checks the current manuscript endpoints with the pinned tools. Its Linux release configuration requires both kernels and includes the unconditional finite-energy endpoints. Run the dedicated command to produce the matching configuration, logs and receipt.

The older source-local audit described above records only the checks that it actually executes. Comparator evidence is produced by the dedicated runner.

## Runtime compatibility

In the restored container the script reuses `runtime/env.sh`'s toolchain configuration and its narrowly scoped process-self path compatibility library. This restores the already permitted process's own executable lookup; it does not alter the Lean executable, kernel, mathematical sources or permissions. The original diagnostic, compatibility source hash, build command and binary hash remain in the runtime restoration evidence. In a normal external installation, the script uses the installed `lake` and verifies the same pinned version.
