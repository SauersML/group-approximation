---
rg: 2
id: dense-homoclinic-algebraic-actions-are-ce
kind: claim
title: Dense homoclinic finite-field algebraic actions have Connes-embeddable crossed products
distinct_from:
  algebraic-compact-action-envelope-for-non-ce-relation: that asks for a non-CE Haar algebraic crossed product; this gives a directly checkable obstruction on its compact module, valid for every sofic replacement actor.
  graph-coset-mixed-module-is-sofic: that proves soficity of one permutation module from finite Schreier models; this applies to non-permutation profinite algebraic actions whenever their finitely supported points are dense.
---

Let `Lambda` be a countable sofic group, let `K` be a compact metrizable
profinite group, and let `Lambda` act on `K` by continuous automorphisms.  If
the homoclinic group

```text
Delta(K,Lambda)={x in K : g x -> 1 as g -> infinity}
```

is dense in `K`, then

```text
L^infinity(K,Haar) rtimes Lambda
```

is Connes embeddable.  If `K` is abelian, Fourier transform identifies this
crossed product with

```text
L(hat(K) rtimes Lambda),
```

so the dual semidirect-product group is hyperlinear.  In particular, such a
crossed product cannot contain the fixed non-Connes-embeddable factor `N`
trace-preservingly.

For a finite-field linear subshift

```text
K <= (F_p^m)^Lambda,
```

the homoclinic group is exactly

```text
K_fin = K intersect (F_p^m)^(Lambda)_{{finite support}}.
```

Indeed convergence to zero at infinity in a finite discrete alphabet is
equivalent to finite support.  Consequently every surviving Haar-linear
envelope over a sofic actor must satisfy the explicit algebraic obstruction

```text
closure(K_fin) != K.                                  (DHA1)
```

This applies in particular to the least-circular replacement actor
`Gamma_Manzoor x SL_3(Z)`, which is residually finite/sofic.  It rules out
every mixed module whose finite-support solutions are dense, whether or not
the module is a permutation or coset module and whether or not the
`SL_3(Z)` image is nonamenable.

Primary inputs: Ben Hayes,
[*Local and doubly empirical convergence and the entropy of algebraic
actions of sofic groups*](https://arxiv.org/abs/1603.06450), Proposition
2.15(ii); and Păunescu's matrix-ultraproduct formulation of sofic p.m.p.
actions, [*On sofic actions and equivalence relations*](https://arxiv.org/abs/1002.0605),
Definition 1.4.
