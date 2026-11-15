# Lean validation files

These stand-alone Lean files exercise the normalized Green formula, the vector-valued Piola identity, and the declaration auditor. Build the proof modules first, then run the files from the repository root.

```sh
lake build +KEBallComparator.Solution
for file in verification/validation/*.lean; do
    lake env lean "$file" || exit
done
```

The [consumer provenance](consumer_provenance.json) records the paths used when the two consumer files were first verified. See the [Comparator guide](../../KEBallComparator/README.md) for the final manuscript and its verification.
