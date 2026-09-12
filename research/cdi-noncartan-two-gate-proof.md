---
rg: 2
id: cdi-noncartan-two-gate-proof
kind: route
title: Combine the projective-basis character criterion with finite-phase central extension
target: cdi-noncartan-bridge-has-two-exact-gates
requires:
  - cdi-property-t-envelope-has-nonabelian-base
  - projective-basis-character-criterion
  - thom-central-corner-criterion
  - finite-index-extensions-preserve-connes-embeddability
---

By `projective-basis-character-criterion`, the images of `H` modulo their
scalar kernel form an orthonormal projective basis of `L^2(Q)` exactly when
`chi` vanishes off `N_chi`.  This proves necessity and sufficiency of `(G1)`
for `Q=L_omega(K)` using the native CDI unitaries.

The same criterion proves that the multiplier can be rephased to
`mu_m`-values exactly when `[omega]` is `m`-torsion.  For such a representative
form

```text
K_tilde=mu_m x_omega K.
```

If `q` is the primitive central projection for the tautological character of
`mu_m`, Fourier decomposition over the finite center gives the
trace-preserving isomorphism

```text
q L(K_tilde) q = L_omega(K)=Q.
```

Were `K_tilde` hyperlinear, its group factor and every positive central
corner would be CE, contradicting non-CE of `Q`.  This proves the compiler.

If `(G1)` fails, Cauchy--Schwarz gives `|chi(h)|=1` exactly on the scalar
kernel, while failure of vanishing gives `0<|chi(h)|<1`; distinct native
projective basis vectors are not orthogonal.  If `(G2)` fails, no rephasing
of this multiplier is finite-valued.  For an infinite central subgroup the
spectral fiber of one character has Haar measure zero in its dual, so it is
not cut out by a nonzero central projection in the canonical group von
Neumann algebra.  This is precisely why Thom's finite central-corner
compiler no longer applies.

The finite-index assertion follows from
`finite-index-extensions-preserve-connes-embeddability`.  Finally, scalarizing
the CDI cocycle `w` changes only the crossed-product multiplier; it does not
replace the coefficient algebra `M_tilde^C` by scalars.  A scalar projective
basis for the full crossed product therefore still requires an independent
group-like basis for the coefficient algebra compatible with the action.

