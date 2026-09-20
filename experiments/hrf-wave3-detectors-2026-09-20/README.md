# Four-hundred-coordinate test for the PSL2(19)-squared cover

The certificate check needs only Python:

```sh
python3 experiments/hrf-wave3-detectors-2026-09-20/verify_cycles.py
```

To regenerate the action, ranks and witnesses, use Python 3.13.13 with
python-flint 0.9.0, as in the preceding wave's environment:

```sh
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave3-detectors-2026-09-20/borel_square_moments.py
```

The small permutation module is justified by prime-to-five transfer
through a Borel-square subgroup. See
`research/wave3-detector-psl19-square-kernel-retention-proof.md`.
The certificate proves nonvanishing of all three central five-twist
directions in one specified finite cover; it makes no claim about
all finite covers or the deeper kernel's entire first homology.
