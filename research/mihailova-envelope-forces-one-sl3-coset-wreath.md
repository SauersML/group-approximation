---
rg: 2
id: mihailova-envelope-forces-one-sl3-coset-wreath
kind: claim
title: A successful mixed Mihailova envelope makes one vertical SL3 coset wreath nonhyperlinear
distinct_from:
  mixed-envelope-finitely-extracts-sl3-module-witness: that produces an unspecified finitely generated SL3-submodule; this uses the exact Mihailova restriction decomposition to reduce all finite multiplicities to one named coset module.
  mihailova-sl3-restriction-is-coset-amplification: that is the algebraic L-set computation; this adds the analytic consequence of a hypothetical non-CE property-T inclusion.
  mihailova-actor-liftable-ce-forces-q-hyperlinear: that extracts finite-dimensional coefficients under projective actor liftability; this makes no liftability assumption and identifies the canonical remaining group through Popa stripping and hyperlinearity locality.
---

Use the Mihailova data of `(MSR1)` with

```text
L=SL_3(Z),
N=ker(F_m->Q),
C=direct_sum_(L/N) C_2,
W_N=C rtimes L.                                       (MEW1)
```

If the fixed non-Connes-embeddable property-`(T)` factor embeds
trace-preservingly in the full mixed Mihailova Haar crossed product over
`Gamma_0 times L`, then `W_N` is nonhyperlinear.

Thus the full mixed candidate has no additional analytic freedom beyond one
explicit arithmetic generalized wreath product.  Proving `W_N` hyperlinear
would refute this Mihailova envelope; proving it nonhyperlinear would already
solve the group goal without the mixed actor.  What remains is the canonical
trace/CE status of the single action `L curvearrowright L/N`.
