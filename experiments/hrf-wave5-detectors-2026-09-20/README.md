# Full coefficient-three square-kernel computation

The root directory records the initially insufficient D20 permutation
module. Its ideal has rank2411, so its16 vanishing sectors alone do
not determine full first homology.

The `c5/` directory contains the successful projective generator and
complete25-tensor computation. See
`research/wave5-detector-psl19-square-kernel-mod-three-proof.md` and
`research/artifacts/hyperbolic-rf-wave5-detectors-2026-09-20.md`.

Python3.13.13, python-flint0.9.0 and NumPy2.5.3 were used. GAP is not
needed to verify stored exact certificates.

```
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/verify_input.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/generator.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/tensor_homology.py --only 4 4
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave5-detectors-2026-09-20/c5/collect_results.py
```

Run the tensor command for each ordered pair i,j in0,...,4 to repeat
all rank computations; omit --only for an uninterrupted complete run.
For shorter individual rank jobs, additionally use --rank-stage with
one of edge0,edge1,edge2,pair01,pair02,pair12,triple. The collector
checks consistency of every recorded stage with the complete output.
The initial22 records are preserved separately; the last three have
individual result files. The largest full tensor and generator were
independently replayed; the other24 rank computations were inspected
in source/output without claiming a second complete execution.

To regenerate proposal certificates, first run construct.py, then
split_normalizer.py and its generated GAP split_decompose.g, followed
by deduplicate.py and its generated GAP isomorphisms.g. These proposal
steps are independently checked by tensor_homology.py and do not need
to be trusted as classification routines.
