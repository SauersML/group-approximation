---
rg: 2
id: full-sl3-root-package-has-an-exact-tracial-hnn-leak
kind: claim
title: The full SL3 root package and relative property T admit an exact tracial HNN leak
distinct_from:
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that gives a conditional MATRIX-ultraproduct countermodel if a crossed product is Connes embeddable; this gives an unconditional exact tracial countermodel and identifies which proof technologies it fences.
  hnn-route-is-relative-commutant-collapse: that reduces nonhyperlinearity to commutant collapse; this records the exact regular-character model showing why root identities and tracial spectral gap alone cannot prove that collapse.
  one-root-p3-denominator-fragment-has-finite-regular-leaks: that is a genuine finite-matrix countermodel for one root; this keeps all lattice roots simultaneously but only in an unrestricted finite tracial algebra.
---

Put

```text
Lambda=SL_3(Z),        Gamma=SL_3(Z[1/3]),
H=<Gamma,t | [t,lambda]=1 (lambda in Lambda)>.         (FTH1)
```

In the group factor `L(H)`, let `rho` be the regular representation
restricted to `Gamma` and `U=lambda_H(t)`.  Then:

```text
tau(rho(g))=delta_e(g)                         (g in Gamma),
[U,rho(lambda)]=1                              (lambda in Lambda),
1-|tau([U,rho(h)])|^2=1                        (h notin Lambda). (FTH2)
```

The last equality follows because `[t,h]` is Britton-reduced and nontrivial,
so its canonical group trace is zero.  Every Steinberg/root relation of
`Gamma`, every conjugacy relation for
`h=diag(3,1,1/3)`, and every relation internal to any parabolic relative-
property-(T) subgroup holds exactly in this model.

Consequently no inequality forcing the `h` trace-square from the lattice
commutators can follow merely from:

1. finite-tracial positivity and trace cyclicity;
2. the exact SL3 root and denominator relations;
3. property (T) or relative property (T) applied to an honest tracial
   representation.

Such an inequality would give `1<=0` in `(FTH2)`.  Relative property (T)
does not bridge the gap: it upgrades almost invariance under the GROUP
specified in its hypothesis, whereas `U` is already exactly invariant under
all of `Lambda`; it supplies no invariance under the external commensurator
`h`.

This does not refute the desired matrix statement, because `L(H)` is not
known to be Connes embeddable.  It proves that a direct bypass must use a
genuinely finite-dimensional/embeddability-sensitive feature of the JOINT
tuple `(rho(Gamma),U)`.  Together with
`one-root-p3-denominator-fragment-has-finite-regular-leaks`, it also shows
that this feature must couple multiple roots at once: single-root pieces
already fail in exact finite matrices.
