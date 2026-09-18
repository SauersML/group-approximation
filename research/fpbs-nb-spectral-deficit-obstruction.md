---
rg: 2
id: fpbs-nb-spectral-deficit-obstruction
kind: claim
title: A Cayley graph with coinciding thresholds has percolation deficit at least its nonbacktracking spectral deficit, which on products is set by the nonamenable factor alone
distinct_from:
  fpbs-ew-nb-majorant: that is the nonbacktracking majorant of the connectivity operator on one regular graph; this turns it into a necessary condition on p_c for every counterexample, compares the two deficits, and applies it through quotient norms to products and to groups with a free quotient.
  fpbs-percolation-kesten-normal-gap: that asks for p_c(G) < p_c(N;G) for every normal N with nonamenable quotient; this is an unconditional nonuniqueness certificate stated through the adjacency norm, with no relative threshold.
  fpbs-gap-survives-product-generator-moves: that tracks the spectral margin 1+h-||A|| under generator moves; this uses the second-order nonbacktracking margin d-1-sigma(||A||) against the percolation deficit d-1-1/p_c.
---

**ESTABLISHED.** Proof in `fpbs-nb-spectral-deficit-obstruction-proof`.

**Setting.** `G = Cay(Gamma,S)` with `S` finite symmetric, `e ∉ S`, `d = |S| >= 3`,
`b = d-1`, adjacency operator `A` on `l2(Gamma)`. Put
`sigma(x) = (x + sqrt(x^2 - 4b))/2` for `x >= 2 sqrt b`, and
`Lambda_G = max(||A||, 2 sqrt b)`.

* **Percolation deficit** `D(G) = d - 1 - 1/p_c(G)`, which lies in `[0, d-1)`.
* **Nonbacktracking spectral deficit** `Delta(G) = d - 1 - sigma(Lambda_G)`.

**Theorem 1 (deficit criterion).** `p_u(G) >= 1/sigma(Lambda_G)`. So
`D(G) < Delta(G)` implies `p_c(G) < p_u(G)`. Equivalently, every Cayley graph
with `p_c = p_u` satisfies `D(G) >= Delta(G)`. If `||A|| >= 2 sqrt b` then
`Delta(G) >= (d - ||A||)(d-1)/(d-2)`, and this is `> 0` iff `||A|| < d`
(nonamenability, by Kesten).

**Theorem 2 (quotient norm).** For every normal `N` with `Q = Gamma/N`, let
`A_X` be the adjacency operator of the Schreier multigraph `X = Cay(Q, pi(S))`
on `l2(Q)`, with a loop for each `s ∈ S ∩ N`. Then `||A|| <= ||A_X||`, so
`Theorem 1` holds with `Lambda = max(||A_X||, 2 sqrt b)`.

**Corollary 3 (products; the class obstruction).** Let `H` and `B` be finitely
generated, with `S = S_H ⊔ S_B`, `d_H = |S_H|` and `d_B = |S_B| >= 1`. Put
`G = Cay(H x B, S) = Cay(H,S_H) □ Cay(B,S_B)`. Then `||A_G|| <= d_B + ||A_H||`.
If `p_c(G) = p_u(G)`, then

```text
D(G) >= d_H - ||A_H||,   and   D(G) >= (d_H - ||A_H||)(d-1)/(d-2) when d_B + ||A_H|| >= 2 sqrt(d-1).
```

The lower bound depends only on `(H, S_H)`. It is the nonamenability deficit
`d_H(1 - rho_H)` of the first factor. No choice of the second factor `B` or of
its generating set shrinks it, however large `d_B` is and whether or not `B` is
amenable.

**Corollary 4 (free quotients; new unconditional windows).** Suppose
`phi: Gamma -> F_m` is onto and `S = {s_1^±1,...,s_m^±1} ⊔ S''`, where
`phi(s_i)` is a free basis, `S'' ⊂ ker phi`, and `|S''| = j`. If

```text
j < (2m-1)(2m - 2 sqrt(2m-1))/(2m-2),
```

then `p_c < p_u` on `Cay(Gamma,S)`. The Benjamini–Schramm spectral bound
`p_u >= 1/||A||` with the same tree subgraph needs `j < 2m-1-2 sqrt(2m-1)`.
The new range is larger by more than one. Concrete new instances: `m = 5`,
`j = 3` or `j = 4`; `m = 4`, `j = 2` or `j = 3`.

An example with `m = 5` and `j = 4` is
`Gamma = Z^2 ⋊_M F_5`, with `a_1` acting by `[[2,1],[1,1]]` and `a_2,...,a_5`
acting trivially, and `S = {a_i^±1} ∪ {e_1^±1, e_2^±1}`. This group:

* has an infinite amenable normal subgroup, so it is not acylindrically
  hyperbolic;
* is not hyperbolic;
* has fixed price one;
* has this Cayley graph given as a twisted rather than Cartesian product. The
  nonunimodular theorem would need a nonunimodular transitive automorphism
  subgroup, and none is exhibited here.

So, as far as recorded in `fpbs-benjamini-schramm-universal`, no imported gap
theorem applies directly to this Cayley graph. Novelty is relative to the
graph, not a literature search. None of this is claimed for `F_2 x Z`
itself.

**What the obstruction kills.** The assignment class is "nonamenable products
with an amenable factor carrying a large generating set, where the gap should
close". By `Corollary 3`, such a graph can have `p_c = p_u` only if
`1/p_c(G) <= d - 1 - (d_H - ||A_H||)`. That is, `p_c` must deviate from the
mean-field value `1/(d-1)` by an amount of order one in the reciprocal, and that
amount is fixed by `H`. Enlarging `S_B` makes `p_u/p_c -> 1` but leaves the
certificate margin untouched. So the gap can close in this class only through
non-mean-field behaviour of `p_c`, never through the spectral side. The single
missing prerequisite for killing the whole class is
`fpbs-product-amenable-factor-mean-field-deficit`.
