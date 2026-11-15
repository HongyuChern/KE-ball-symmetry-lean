# Verification of the final manuscript

The Linux release check ran on the clean source commit `d75a2ea960ef2f169d594ee60e4755204d0ff3f3`. The [receipt](receipt.json) records all seven targets, the final manuscript hash, the locked dependencies, executable hashes, and the success markers from Lean and Nanoda. The [environment record](environment.txt) and the original [Comparator log](comparator.log) and [tool build log](build.log) accompany it.

The release tag adds the evidence and editorial documentation to that source commit. The Comparator input hashes match the tagged files. To reproduce the full Comparator run, follow the [Linux verification instructions](../KEBallComparator/README.md). To check the saved evidence against an extracted release tree, run the following command from its root.

```sh
python3 tools/run_comparator.py --verify-receipt verification/receipt.json
```
