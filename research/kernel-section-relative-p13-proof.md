---
rg: 2
id: kernel-section-relative-p13-proof
kind: route
title: Expand the finite quotient multiplication cocycles in the free kernel basis
target: kernel-section-builds-relative-p13-chart
requires:
  - triangle-colimit-llp-reduces-to-relator-local-splitting
  - gowers-hatami-finite-group-hs-stability
  - finite-subgroup-near-regular-has-large-regular-core
---

The quotient map `q:E->P_13` is injective on `P_1` and on `P_3`, and the two
copies meet in the same `P_0`.  Hence a section can be chosen to agree with
the inclusions on `P_1 union P_3`.

For `g,h in P_13`, put

```text
c(g,h)=sigma(g)sigma(h)sigma(gh)^(-1) in N.              (KSP6)
```

The group `P_13` is finite.  Every `c(g,h)` is therefore one of finitely
many fixed elements of the free group on `n_1,...,n_r`; their maximal reduced
length is the finite number `L_sigma` in `(KSP2)`.

If a reduced kernel word is

```text
c=n_(a_1)^eps_1 ... n_(a_l)^eps_l,
```

unitary invariance and telescoping give

```text
||rho(c)-I||_2
 <=sum_j ||rho(n_(a_j)^eps_j)-I||_2
 <=l d.                                                   (KSP7)
```

Since `rho` is an exact representation of `E`, `(KSP6)` and `(KSP7)` imply

```text
||psi(g)psi(h)-psi(gh)||_2
 =||rho(c(g,h))-I||_2
 <=L_sigma d,
```

which proves `(KSP4)`.  The normalization of the section proves `(KSP5)`.

Apply fixed-finite-group flexible HS stability to the all-pairs table
`psi`.  On a regular microstate branch, every fixed nonidentity word
`sigma(g)` has trace tending to zero; it is nonidentity because its quotient
is `g`.  Hence `psi` has asymptotically regular character.  Trace continuity
under the exactification and the finite-subgroup regular-core theorem give
the final regular-core assertion.
