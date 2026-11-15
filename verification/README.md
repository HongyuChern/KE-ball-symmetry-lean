# Verification

The Linux release configuration checks all seven Comparator targets using Lean and Nanoda. The [receipt](receipt.json) records the verified source commit, manuscript hash, dependency revisions, executable hashes, and results. The original [Comparator log](comparator.log), [tool build log](build.log), and [environment record](environment.txt) accompany it.

To check the saved evidence against the current tree, run the following command from the repository root.

```sh
python3 verification/run_comparator.py --verify-receipt verification/receipt.json
```

See the [Linux instructions](../KEBallComparator/README.md) to rerun both kernels. The [validation files](validation/) are stand-alone Lean checks, and [audits/](audits/) contains the earlier declaration-specific probes.
