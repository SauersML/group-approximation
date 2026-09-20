# Exact square-kernel mod-five computation

See `research/artifacts/hyperbolic-rf-wave4-detectors-2026-09-20.md` and
`research/wave4-detector-psl19-square-kernel-mod-five-proof.md`.

Python3.13.13, python-flint0.9.0 and NumPy2.5.3 reproduce the result.
The stored GAP summand certificate is independently checked, so GAP
is not needed for verification:

```
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave4-detectors-2026-09-20/tensor_homology.py
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave4-detectors-2026-09-20/a4_generator.py
```

The helper source imports the finite coset construction prefix of
`borel_a4_homology.py`, stopping before its separate cover elimination.
This deliberately shares the audited group and coset enumeration.
GAP can regenerate the proposal via `projective_decomposition.py`
followed by `gap --bare -q --quitonbreak decompose.g`. Its choice of
summand bases may differ; the verification accepts any exact direct
sum satisfying all intertwining and cohomology checks.
