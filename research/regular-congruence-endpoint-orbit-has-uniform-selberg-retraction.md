---
rg: 2
id: regular-congruence-endpoint-orbit-has-uniform-selberg-retraction
kind: claim
title: Regular congruence endpoint pairs retract uniformly to the exact commutant orbit
distinct_from:
  odd-congruence-iwahori-pairs-have-uniform-linear-repair: that permits unequal representation types and repairs their small complements by trivial blocks; equal regular characters here complete the polar intertwiner inside the original types and identify the result with the exact endpoint orbit.
  congruence-iwahori-endpoint-fiber-contains-core-commutant-orbits: that classifies the zero set and exhibits macroscopic bending inside it; this proves a uniform quantitative retraction onto that zero set once both vertex actions are authenticated regular congruence representations.
  iwahori-uniform-infinitesimal-rigidity: that is a degree-one derivative gap; this is a global normalized-HS averaging and polar-completion estimate with no Taylor expansion.
  iwahori-unitary-commutant-transfer: that asks for centralizer transfer for arbitrary exact modular vertex representations; this only treats two representations of one odd congruence quotient with equal total character, the regular block needed after authentication.
---

Let `Q` be any odd congruence quotient occurring in the Iwahori system and
let

```text
rho,eta:Q -> U(d)
```

be exact representations with the same character; in particular both may
be the same multiple of the regular representation.  Let `S_B` be the fixed
Iwahori edge generating set, whose image generates `Q`, and put

```text
epsilon=max_(s in S_B)||rho(s)-eta(s)||_2.             (SOR1)
```

There is a constant `kappa>0`, independent of `Q`, its level, its regular
multiplicity and `d`, and a unitary exact intertwiner `V` such that

```text
rho(g)V=V eta(g)                 (g in Q),
||V-I||_2<=4 epsilon/kappa.                            (SOR2)
```

Consequently, for every distinguished endpoint element `w in Q`,

```text
||eta(w)-rho(w)||_2<=8 epsilon/kappa.                  (SOR3)
```

In particular, for the canonical endpoint orbit

```text
O={U^*rho(w)U:U in rho(K)'},
```

one has the quantitative orbit-distance bound

```text
dist_2(eta(w),O)<=8 epsilon/kappa,                     (SOR4)
```

because `rho(w)` itself belongs to `O`.

If `rho` and `eta` already agree exactly on the retained square-free core
`K=<r,t>`, then `(SOR2)` puts `V in rho(K)'`, and

```text
eta(w)=V^*rho(w)V
```

lies exactly in the endpoint orbit

```text
O={U^*rho(w)U:U in rho(K)'}.                           (SOR5)
```

Thus orbit synchronization has a dimension- and level-independent linear
solution on the authenticated regular congruence sector.  There is no
nonlinear normalized-HS Taylor remainder: conditional expectation is
linear, and polar completion pays only the squared missing rank.

The hypothesis that `eta` is an exact congruence representation with the
same character is load-bearing.  It is not supplied by the five square-free
presentation defects; that interface is fenced by
`selberg-orbit-retraction-does-not-cross-square-free-basin`.
