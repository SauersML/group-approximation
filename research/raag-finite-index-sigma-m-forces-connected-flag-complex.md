---
rg: 2
id: raag-finite-index-sigma-m-forces-connected-flag-complex
kind: claim
title: If a finite-index subgroup of a right-angled Artin group has a nonempty Sigma^m invariant, the flag complex is (m-1)-connected
artifacts:
  - research/artifacts/zp-raag-virtual-kernels-2026-09-13-part2.md
distinct_from:
  raag-virtual-fp-n-kernel-forces-acyclic-flag-complex: that concludes acyclicity of L from a kernel of type FP_n by Betti numbers over division rings; this concludes connectivity of L (and acyclicity over any ring) from a single nonempty Sigma-invariant by a geometric argument at infinity.
---

Let `L` be a finite flag complex, `H ≤ A_L` a subgroup of finite index, `m ≥ 1`, and `R` a
commutative ring.

1. If the homotopical Bieri--Neumann--Strebel--Renz invariant `Σ^m(H)` is nonempty, then `L`
   is `(m−1)`-connected.
2. If `Σ^m(H; R)` is nonempty, then `L` is `(m−1)`-acyclic over `R`.

Only one character class is needed; its negative need not lie in the invariant.

Idea of proof. Perturb the character (the invariant is open) so that its averaged slope on
every generator is nonzero. At the vertex `1` of the CAT(0) cube complex `X̃`, the union of
the flat orthants in the ascending generator directions is a cone over a copy of `L`, and
the sphere `S_R` of radius `R` in it sits at height at least `cR − C'`. Geodesic direction at
`1` followed by forgetting signs retracts `X̃ ∖ {1}` onto `|L|` and is a homeomorphism on
`S_R`. The geometric criterion for `Σ^m` null-homotopes spheres of `S_R` inside a half-space
missing `1`, which forces them to be null in `L`.

Consequence: Zaremsky's Problem 1.19 has the answer yes (with the Bestvina--Brady theorem);
see `raag-virtual-fn-kernel-conjecture-via-sigma-invariants`.

Proof: artifact part 2, Theorem 7. UNREVIEWED as of 2026-09-13 (review requested from
z-verify-topology); novelty unchecked.
