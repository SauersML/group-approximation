# STW XXII: all-finite-factor dimension-three breakthrough audit

## Result

Two independently audited degree-two theorems cover the exhaustive
dichotomy of finite factors. Normalized matrix algebras have the universal
weighted two-sphere modulus `epsilon_0^3/276480`; separable-predual diffuse
II1 factors have the universal modulus `epsilon_0^3/216000000`. Their
minimum is therefore one modulus for every finite factor. Both branches
also prove global two-connectivity.

## Why mixed fibre type causes no gap

The stabilized weighted-copy multifunction was already proved nonempty,
closed, and lower semicontinuous by a finite-factor correction estimate
that does not distinguish type. The new topological input is also
type-free after taking the minimum of the two numerical moduli. Michael
selection is applied to the family of values in one fixed Hilbert space;
it does not choose a proof, a matrix size, or a type stratum continuously.
Thus matrix size and factor type may vary arbitrarily across the base.

## Michael checklist

```text
base:       compact Hausdorff, hence paracompact; dim <=3
ambient:    one complete (ell^2)^m from module stabilization
values:     nonempty, closed in operator balls, lower semicontinuous
topology:   common LC^0, LC^1, LC^2 moduli; every value 2-connected
recovery:   fibrewise contractions return to M by the operator-ball identity
```

These are exactly the hypotheses of the finite-dimensional selection
theorem with `n=2`.

## Trace-gap quantifiers

For each fixed spectral cut and every replication number `m`, the
`m`-dependent neighbourhood cutoff equals one at the chosen base point, so
the quotient class is unchanged. The sum of the orthogonal range positives
is a positive contraction. Hence `m sigma([c])<=||sigma||` for every `m`.
First `m->infinity`, then removal of the spectral cut, kills every bounded
positive fibre-gap trace.

## Scope

This proves the trace theorem for every countably generated factorial
bundle over a compact Hausdorff base of covering dimension at most three.
The next selection obstruction is degree three (`S^3` fillings) for
four-dimensional bases, not variation between matrix and diffuse fibres.

Inputs independently audited: `stw22-matrix-weighted-copy-uniform-s2-fillings`,
`stw22-diffuse-weighted-copy-uniform-s2-fillings`,
`stw22-stabilize-l2-bundle-and-select-weighted-copies-proof`, and
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity`.