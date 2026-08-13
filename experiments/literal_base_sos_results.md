# Literal-base scalar Laplacian SOS screen

Date: 2026-08-13

## Question

Can the property-`(T)` input for the literal six-generator base in
`non_mf_groups_exist.tex` be closed by a small-support scalar group-ring
certificate

```text
Delta^2 - c Delta = sum_i xi_i^* xi_i,
```

using only reductions that replay the twenty displayed relators?

`literal_base_laplacian_sos.py` supplies the proof-carrying reducer.
`literal_base_sos_sdp.py` uses that reducer to discover a numerical Gram
matrix.  Solver output is not a proof; any positive candidate would still
have to be rationalized and checked by Lean through
`LiteralBaseSOS.IsRationalCertificate`.

## Results

The small supports give no credible positive gap.

| radius | support | coefficient classes | numerical gap | maximum feasibility error | verdict |
|---:|---:|---:|---:|---:|:---|
| 0 | 1 | 97 | infeasible | -- | support cannot express `Delta^2` |
| 1 | 12 | 97 | `-1.65e-12` | `2.94e-13` | zero gap |
| 2 | 97 | 4553 | `7.01e-9` | `1.18e-8` | numerically zero |

The radius-one solution has numerical rank one and maximum eigenvalue 132;
it is the expected zero-gap factorization of `Delta^2`, not a Kazhdan
certificate.  At radius two the purported positive objective is smaller
than the PSD/constraint violation, so it cannot be interpreted as signal.

A radius-three ball has 684 words.  Even a deliberately coarse 100-iteration
probe did not complete within 55 seconds on four Milan cores.  It was stopped
instead of launching a long blind SDP.  The jump from a 97-by-97 to a
684-by-684 dense semidefinite variable makes this a poor iteration path.

## Consequence for the proof search

Do not spend further compute on the current dense scalar radius expansion
without first changing the formulation.  Higher-yield alternatives are:

1. an affine relative-`(T)` decomposition, combining a certified
   `SL_3(Z)` gap with a translation-moving-projection estimate;
2. a sparse/chordal scalar SOS formulation with exact relator replay; or
3. a direct formalization of the classical property-`(T)` theorem for
   `Z^3 semidirect SL_3(Z)`.

The analytic non-MF theorem and the literal marked-word witness do not depend
on this experiment.  The only open formal endpoint is the unconditional
Lean proof of property `(T)` for the literal base; the manuscript correctly
uses the published theorem as an external input.

## Reproduction

On MSI, after loading the project Python environment:

```text
python3 experiments/literal_base_sos_sdp.py \
  --radius 2 --max-iterations 20000 --tolerance 1e-8 \
  --result-output experiments/literal-base-r2-result.json
```

The optional `--result-output` is intentional: it preserves the complete
JSON summary even when a remote wrapper does not relay standard output.
