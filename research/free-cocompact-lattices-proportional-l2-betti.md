---
rg: 2
id: free-cocompact-lattices-proportional-l2-betti
kind: claim
title: Groups acting freely and cocompactly on one complex have covolume-proportional L2-Betti numbers
distinct_from:
  algebraic-strong-atiyah-counterexample-exists: that asks for one torsion-free group with a non-integral kernel dimension; this is a proportionality theorem that transfers kernel dimensions between any two groups acting freely and cocompactly on the same complex.
artifacts:
  - research/artifacts/atiyah-lattice-transfer-2026-09-12.md
---

**ESTABLISHED** by [[free-cocompact-lattices-l2-proportionality-proof]].

Let `X` be a connected locally finite simplicial complex, and let `G, Γ ≤ Aut(X)` be
discrete subgroups acting freely on simplices (no nontrivial element maps a simplex
to itself) and cocompactly. Then for every `k`

```text
b_k^(2)(X;Γ) = r · b_k^(2)(X;G),        r = |Γ\X_0| / |G\X_0|  in  Q_(>0).
```

Here `b_k^(2)(X;D) = dim_(N(D)) ker Δ_k`, where `Δ_k` is the combinatorial Laplacian on
`ℓ²(X_k)`, a matrix over `Z[D]` once orbit representatives are oriented.

## Transfer

- If `Γ` is torsion-free and `b_k^(2)(X;G)` is irrational, the Laplacian
  `Δ_k in M_(n_k)(Z[Γ])` has irrational kernel dimension. That refutes Strong
  Atiyah for `Γ` (route `atiyah-counterexample-via-lattice-transfer`).
- Contrapositive: if a torsion-free group satisfying Strong Atiyah acts freely and
  cocompactly on `X`, then every group `G` acting freely and cocompactly on `X`,
  with or without torsion, has `b_k^(2)(X;G) in (1/r)Z`.

## Credit

The group form, for lattices in a common lcsc unimodular group, is the
proportionality principle of Gaboriau (measure equivalence invariance) and
H. D. Petersen (arXiv:1104.3294). Those statements were not read from source here
and nothing is imported from them. The proof route is self-contained: harmonic
diagonals are `Aut(X)`-invariant, and Haar unfolding counts orbits. No novelty is
claimed for the principle.
