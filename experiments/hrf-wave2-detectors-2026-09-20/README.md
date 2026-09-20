# Explicit PSL2(19) triangle kernel calculation

`psl19_kernel.py` enumerates the 3420 projective determinant-one matrices
over F19, chooses the recorded exact order-five triple, checks pairwise
generation and all three link girths, and calculates the integral first
homology of the canonical finite-index kernel.

Environment used: Python 3.13.13 and python-flint 0.9.0. For example:

```sh
uv venv --python python3.13 /tmp/hrf-wave2-py313
uv pip install --python /tmp/hrf-wave2-py313/bin/python python-flint==0.9.0
/tmp/hrf-wave2-py313/bin/python experiments/hrf-wave2-detectors-2026-09-20/psl19_kernel.py
```

The script uses exact integer and rational arithmetic. The first 1962
eliminations are explicit unimodular unit-pivot operations on the
tree-collapsed cellular boundary. The remaining 88 by 1458 matrix is
saved in `psl19_residual.json`. Its Smith form has 88 unit invariant
factors; independently, its transpose Hermite form is an 88 by 88
identity above zero rows. Both checks use FLINT, not separate proof
kernels. The full calculation is written computational evidence, not
Lean certification.

`psl19_kernel_result.json` and `psl19_kernel.out` record the exact
matrices, link girths, homology result, and run diagnostics. No sampled
finite-quotient search is used to infer residual finiteness or persistence.

`psl19_quotient_census.py` needs only the Python standard library. It
checks all pairs from the two 20-element projective edge centralizers
and records a second compatible vertex-conjugation configuration. The
explicit configuration certifies a surjection from the triangle onto
`PSL2(19) x PSL2(19)` by the elementary subdirect-product argument in
the associated Cairn proof. No enumeration of this larger product is
needed, and its deeper kernel's homology has not been computed.
