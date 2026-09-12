---
rg: 2
id: finite-character-hecke-intersection-formula
kind: claim
title: Finite character Hecke coefficients are exactly measured by subgroup intersections
root: true
artifacts:
  - research/finite-character-hecke-intersection-formula-proof.md
distinct_from:
  canonical-marked-reynolds-return-is-subgroup-intersection: that computes an adjoint Reynolds overlap after quotienting a central mark; this computes the original character-idempotent coefficient, including its phase-compatibility dichotomy.
  finite-character-idempotents-have-exact-hnn-transport: that gives exact covariance under one HNN edge; this gives a necessary-and-sufficient orthogonality test for arbitrary transported finite-subgroup character idempotents.
  finite-bad-character-packing-extension: that asks for a large trace-compatible packing; this turns its orthogonality clause into an explicit finite subgroup-intersection condition.
---

Let `H,K` be finite subgroups of a group `G`, let `chi` and `psi` be
one-dimensional unitary characters of `H` and `K`, and put

```text
e_(H,chi)=|H|^(-1) sum_(h in H) overline(chi(h)) h,
e_(K,psi)=|K|^(-1) sum_(k in K) overline(psi(k)) k.     (FCH1)
```

For `g in G`, set

```text
I=H intersect g K g^(-1),
psi^g(a)=psi(g^(-1) a g)                 (a in I).     (FCH2)
```

In the canonical Hilbert space `ell^2(G)`, one has the exact dichotomy

```text
||e_(H,chi) g e_(K,psi)||_2^2
 = |I|/(|H||K|),       if chi|I=psi^g|I,
 = 0,                  otherwise.                     (FCH3)
```

Consequently

```text
e_(H,chi) g e_(K,psi)=0
 iff chi and psi^g disagree on I.                      (FCH4)
```

For a finite family `H_i<=G`, characters `chi_i`, and elements `g_i`, put

```text
p_i=g_i e_(H_i,chi_i) g_i^(-1).                       (FCH5)
```

Then `p_i p_j=0` exactly when the transported characters disagree on

```text
g_i H_i g_i^(-1) intersect g_j H_j g_j^(-1).          (FCH6)
```

If they agree, the nonzero overlap has the fixed regular norm

```text
||p_i p_j||_2^2
 = |g_i H_i g_i^(-1) intersect g_j H_j g_j^(-1)|
   /(|H_i||H_j|).                                     (FCH7)
```

Thus simultaneous character packing is a finite labelled-intersection
problem.  There is no approximate or representation-dependent
orthogonality left to verify once the subgroup intersections and their
transported character labels are known.
