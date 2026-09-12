---
rg: 2
id: fixed-flip-negative-corner-is-sofic
kind: claim
title: The negative corner of a fixed-flip permutation model is sofic
distinct_from:
  slofstra-involution-not-sofic-radical: that constructs one permutation-ultraproduct model detecting the full solution-group sign; this identifies the approximation class of its negative spectral corner.
  finite-predicate-signed-permutation-sector: that classifies finite predicate packet sectors inside one exact finite group; this treats an asymptotic group representation obtained from central flip corners.
---

**ESTABLISHED SIGNED-CORNER THEOREM.** Let `Gamma=<X:R>` be finitely
presented and suppose there are maps

```text
rho_n:X union {J} -> Sym(Omega_n)                         (FNC1)
```

whose relator Hamming defects tend to zero, where `rho_n(J)=j_n` is an exact
fixed-point-free involution and the centrality defects

```text
d_H([rho_n(x),j_n],1) -> 0       (x in X)                 (FNC2)
```

vanish. After changing each `rho_n(x)` on `o(|Omega_n|)` points, it may be
assumed to commute exactly with `j_n`. On the negative eigenspace

```text
V_n^- = ker(j_n+1),                                      (FNC3)
```

the corrected permutations act by signed permutation matrices. Hence they
define a homomorphism

```text
theta_-:Gamma -> product_omega (C_2 wr Sym(d_n))          (FNC4)
```

for normalized Hilbert--Schmidt metric, with `d_n=dim(V_n^-)`.

The image of `(FNC4)` is sofic. More precisely the standard embedding of a
signed permutation into `Sym(2d_n)` is bi-Lipschitz, uniformly in `n`, between
normalized Hilbert--Schmidt distance squared and Hamming distance. Therefore
the tracial image quotient

```text
Gamma/ker(theta_-)                                       (FNC5)
```

is a sofic group. In particular no nontrivial word of this quotient lies in
its sofic radical.

DERIVATION
fixed-flip-negative-corner-proof
