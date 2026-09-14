---
rg: 2
id: support-three-zero-divisor-differences-bounded-quasimorphism
kind: claim
title: Every homogeneous quasimorphism is at most three times its defect on the differences of a support-three zero divisor
distinct_from:
  zero-divisor-supports-have-no-quasimorphism-isolated-extremes: that forbids isolated extremes on supports of any size; this is the sharper bound on all three differences when the support has three points.
  kaplansky-zero-divisor-conjecture: that is the conjecture; this is an established necessary condition on support-three counterexamples.
  cyclic-centralizer-groups-have-no-support-three-zero-divisors: that is the open host-class statement; this is a quantitative constraint on the support in every torsion-free host.
---

**ESTABLISHED.** Let `G` be torsion-free, `k` a field, and `alpha in k[G]` a left
or right zero divisor with `supp alpha = {a_0, a_1, a_2}`. For every
homogeneous quasimorphism `phi` on `G` (definitions as in
`zero-divisor-supports-have-no-quasimorphism-isolated-extremes`) and all `i, j`,

```text
|phi(a_i^-1 a_j)| <= 3 D(phi).
```

**Consequences.**
1. Every homomorphism `G -> R` vanishes on each `a_i^-1 a_j`, so these elements
   have finite order in `H_1(G; Z)`.
2. If `a_i^-1 a_j in [G, G]`, then `scl_G(a_i^-1 a_j) <= 3/2`. This uses Bavard
   duality, quoted from D. Calegari, *scl* (MSJ Memoirs 20, 2009), text
   extracted on MSI from the author's PDF: "Theorem 2.70 (Bavard's Duality
   Theorem, [8]). Let G be a group. Then for any a ∈ [G,G], we have an equality
   scl(a) = 1/2 sup_{φ∈Q(G)/H^1(G;R)} |φ(a)|/D(φ)". The extracted text renders
   the quotient slash as "=". His Definition 2.20 calls a quasimorphism
   homogeneous if φ(a^n) = nφ(a) for all a ∈ G and n ∈ Z, and "Denote the
   vector space of homogeneous quasimorphisms on G by Q(G)". The defect D(φ)
   is his Definition 2.15.
   The same bound holds for `a_i a_j^-1`, which is conjugate to `a_j^-1 a_i`.
3. *Sieve.* A support triple is excluded in any torsion-free group carrying one
   homogeneous quasimorphism, such as a Brooks counting quasimorphism, with
   `|phi(a_i^-1 a_j)| > 3 D(phi)` for some pair.

*Scope.* Elementary, from the positive relations of
`zero-divisor-support-vertex-cones-contain-positive-relations`. No sharpness of
the constant `3` is claimed. No novelty is claimed.

DERIVATION
[[support-three-zero-divisor-quasimorphism-bound-proof]]
