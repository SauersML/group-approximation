---
rg: 2
id: exact-cuspidal-hadamard-cross-block-proof
kind: route
title: Apply the restriction-fiber gap and mix two equal-core cuspidal endpoints
target: exact-cuspidal-hadamard-mixing-has-macroscopic-cross-blocks
requires:
  - cuspidal-redistribution-refutes-regular-core-orbit-basin
  - congruence-endpoint-orbits-are-restriction-ring-fibers
---

Fix a prime `p=1 mod 4` for which there are two distinct cuspidal
irreducibles `delta_1,delta_2` of `Q_p=PSL_2(F_p)`.  The character-table
calculation in
`cuspidal-redistribution-refutes-regular-core-orbit-basin` gives

```text
dim(delta_1)=dim(delta_2)=d_0=p-1,
Res_(B_p)(delta_1)=Res_(B_p)(delta_2).                 (ECHP1)
```

Choose an intertwining unitary once and use it to identify the two
restriction spaces, so both restrictions are literally one representation
`beta_p` on `H_p`.

Apply `congruence-endpoint-orbits-are-restriction-ring-fibers` to this fixed
core.  The two endpoint multiplicity vectors are the two distinct unit
vectors `e_(delta_1)` and `e_(delta_2)`.  Their weighted overlap in `(ERF3)`
is zero, while the common dimension is `d_0`; hence

```text
mu(e_(delta_1),e_(delta_2))=1.                         (ECHP2)
```

The lower inequality in `(ERF4)` therefore says that the two complete
endpoint orbits over `beta_p` are at normalized Hilbert--Schmidt distance at
least the quotient-independent constant `kappa>0`.  Writing
`X_i=delta_i(x)`, the pair `(X_1,X_2)` is one particular pair of points in
those two orbits.  Consequently

```text
||X_1-X_2||_(2,d_0)
  >=dist_2(O_(delta_1),O_(delta_2))
  >=kappa.                                               (ECHP3)
```

This proves `(ECH2)` without choosing a quotient-dependent intertwiner or
spectral-gap constant.

It remains to compute the advertised exact model.  On `H_p (+) H_p` put

```text
W=2^(-1/2) [ 1   1 ] .                                  (ECHP4)
             [ -1  1 ]
```

Because the two core restrictions are literally equal, `W` commutes with
`beta_p (+) beta_p`.  Conjugating the exact representation
`delta_1 (+) delta_2` by `W` therefore leaves every core letter fixed and
preserves every endpoint relation exactly.  Direct block multiplication
gives its extending involution as

```text
X'=W diag(X_1,X_2) W^*
  =(1/2) [ X_1+X_2    -X_1+X_2 ] .                      (ECHP5)
          [ -X_1+X_2   X_1+X_2 ]
```

Thus the two off-diagonal blocks are both `(X_2-X_1)/2`.  Their total
squared Frobenius mass, normalized by the full dimension `2d_0`, is exactly

```text
(1/(2d_0)) * 2 * (1/4)||X_2-X_1||_F^2
  =(1/4)||X_2-X_1||_(2,d_0)^2
  >=kappa^2/4.                                          (ECHP6)
```

Finally, refine `beta_p` into its complete cyclic-packet decomposition and
use the same refinement in both displayed copies.  Every resulting packet
projection has the form `diag(P,P)`, so it still commutes with `W`.  Hence
the calculation `(ECHP5)--(ECHP6)` is unchanged after refinement and gives
the claimed macroscopic cross-packet mass.
