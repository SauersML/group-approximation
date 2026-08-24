---
rg: 2
id: finite-character-packing-extension-is-clique-lp
kind: claim
title: Finite character packing-extension is a colored clique and rational feasibility problem
root: true
artifacts:
  - research/finite-character-packing-extension-is-clique-lp-proof.md
requires:
  - finite-character-hecke-intersection-formula
distinct_from:
  finite-bad-character-packing-extension: that asks for ambient finite groups satisfying packing and trace extension; this gives a complete decision procedure and exact certificates once a candidate finite group is specified.
  finite-packet-multiplicity-certificates-detect-mf-radicals: that certifies vanishing consequences of homogeneous packet equations; this decides simultaneous conjugate orthogonality and a prescribed inhomogeneous trace restriction.
  semidirect-bad-orbit-needs-zero-trace-support: that treats automorphism orbits in a semidirect product; this applies to arbitrary finite ambient groups and arbitrary transported subgroup intersections.
---

Fix a finite group `G`, finite subgroups `H_1,...,H_M<=G`,
one-dimensional characters `chi_i` of `H_i`, and rational probability
distributions `mu_i` on `Irr(H_i)`.

There is a finite graph `X_G` with vertices represented by pairs `(i,g)`,
`g in G`, such that two distinct vertices are adjacent exactly when

```text
(g e_(H_i,chi_i) g^(-1))
(h e_(H_j,chi_j) h^(-1))=0.                           (CLP1)
```

The adjacency relation is computed solely from the subgroup intersection

```text
g H_i g^(-1) intersect h H_j h^(-1)                  (CLP2)
```

and the two transported character labels.  A family containing `K_i`
pairwise orthogonal conjugates of every forbidden idempotent exists exactly
when `X_G` has a clique containing `K_i` vertices of colour `i` for every
`i`.

The prescribed distributions `mu_i` extend simultaneously to a tracial
state on `C^*(G)` exactly when the following rational linear program is
feasible.  Choose numbers

```text
lambda_pi>=0                 (pi in Irr(G)),
sum_pi lambda_pi=1,                                      (CLP3)
```

such that for every `i` and `sigma in Irr(H_i)`,

```text
mu_i(sigma)
 =sum_(pi in Irr(G)) lambda_pi
   [Res_(H_i)^G pi:sigma] dim(sigma)/dim(pi).          (CLP4)
```

Consequently, for a fixed finite candidate `G`, character packing with
exact trace extension is decidable by finite exact arithmetic.  A positive
instance has two finite certificates: a coloured clique and a rational
feasible point `(lambda_pi)`.  A negative trace-extension instance has a
rational separating functional by linear-programming duality; a negative
packing instance has an exhaustive finite clique certificate.

This separates the two difficulties sharply.  Orthogonality is controlled
by labelled subgroup intersections, while exact tracial extendability is
controlled by the restriction matrix from `Irr(G)` to the context groups.
Neither requires matrix-size limits or analytic approximation estimates.
