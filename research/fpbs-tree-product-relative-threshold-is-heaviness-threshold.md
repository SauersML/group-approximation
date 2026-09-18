---
rg: 2
id: fpbs-tree-product-relative-threshold-is-heaviness-threshold
kind: claim
title: On a tree times any infinite Cayley graph, the relative threshold of the fibre subgroup is the heaviness threshold of the end-fixing group, so Claim E there is Hutchcroft's question p_t = p_h
distinct_from:
  fpbs-relative-threshold-is-quotient-l2-threshold: that is the open Claim E, p_c(N;G) = p^Q_(2->2)(N;G), on every pair; this proves a different identity, p_c(N;G) = p_h, on tree products, which turns Claim E there into the named open question p_t = p_h without proving it.
  fpbs-amenable-wq-normal-pu-is-relative-pc: that identifies p_c(H;G) with p_u for amenable H; this identifies p_c(N;G) with p_h for every infinite fibre group, amenable or not, and recovers p_h = p_u in the amenable case only by combining with that node.
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports p_c < p_h <= p_u; this computes p_h exactly on tree products as a relative threshold of a subgroup, which that import does not do.
  fpbs-hp-relative-sharpness: that is the imported exponential tail below p_c(H;G); this uses it only to pass from infinite mean to an almost sure fibre-infinite cluster.
  fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab: that imports Timar's slab theorem for general pairs; this applies it to tree products, where slab components are finite unions of fibres.
---

**ESTABLISHED.** Proof route:
`fpbs-tree-product-heaviness-threshold-proof`.

**Setting.** This is the setting of the tree-product fibre-operator claim of
wave 12.

- `Lambda` is a finitely generated group with finite symmetric generating set
  `S_Lambda` such that `T = Cay(Lambda,S_Lambda)` is the `k`-regular tree,
  with `k >= 3`.
- `H_grp` is any infinite finitely generated group, `S_H` a finite symmetric
  generating set, and `H = Cay(H_grp,S_H)`.
- `Gamma = Lambda x H_grp` with `S = S_Lambda ⊔ S_H`, so
  `G = Cay(Gamma,S) = T x H` (Cartesian product).
- `N = {1} x H_grp`. The fibre over `v in Lambda` is `F_v = {v} x H_grp`, and
  `F_1 = N`.
- `p_c(N;G) = sup{p : E_p|K_o ∩ N| < infinity}`. By
  `fpbs-hp-relative-sharpness` (see Step 0 of the proof) this equals
  Hutchcroft--Pan's `inf{p : some cluster meets N infinitely, a.s.}`.
- Fix an end `xi` of `T` and put `Gamma_xi = Aut_xi(T) x H_grp`, acting
  coordinatewise, with `H_grp` acting on `H` by left multiplication.
  `Gamma_xi` is a closed, transitive, nonunimodular subgroup of `Aut(G)`.
- `p_h = p_h(G,Gamma_xi)` is the heaviness threshold, and
  `p_t = p_t(G,Gamma_xi)` the tiltability threshold, both as in Hutchcroft
  arXiv:1711.02590 (definitions in
  `fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab`).

**Theorem.**

```text
p_c(N;G) = p_h(G, Gamma_xi).
```

More precisely, for every `p > p_h` the number of heavy clusters is almost
surely 1 or almost surely infinite. In the first case every point of the fibre
`F_o` connects to `o` with probability at least `theta_h(p)^2 > 0`. In the
second case some cluster meets some fibre in an infinite set. Conversely, a
cluster meeting a fibre infinitely is heavy.

## Consequences

1. **Claim E on tree products is exactly `p_t = p_h`.** Wave 12 proves
   `p^Q_(2->2)(N;G) = p_t(G,Gamma_xi)` on these graphs
   (`fpbs-tree-product-fibre-operator-is-half-tilted-susceptibility`, part 1,
   on the swarm branch). So `E(G,N)`, i.e. `p_c(N;G) = p^Q_(2->2)(N;G)`,
   holds iff `p_t(G,Gamma_xi) = p_h(G,Gamma_xi)`. For `H = Z^d` this is
   Hutchcroft's Question Q2(1) (arXiv:1711.02590v3, Section 8): "Let $T_k$
   be a $k$-regular tree, let $d\geq 1$ and consider the group of
   automorphisms $\Gamma$ of $T_k \times \Z^d$ that fix some specified end
   $\xi$ of $T$.", whose item 1 is "Is $p_t=p_h$?". The open fibre
   square-root law of wave 12
   (`fpbs-tree-product-fibre-square-root-law-below-relative-threshold`) is
   therefore the same statement as `p_t = p_h` for `T x H`, now for arbitrary
   infinite `H`.
2. **Where a counterexample to Claim E must come from.** A failure of `E` on
   a tree product is precisely a pair with `p_t < p_h`. Hutchcroft shows that
   `p_t < p_h` does occur for other nonunimodular pairs (line 516: "both
   equality and strict inequality between $p_t$ and $p_h$ are possible"). His
   strict example uses a different group, the `(1,1,2)`-orientation group
   `Gamma'` of the 4-regular tree, so it says nothing about `Gamma_xi` on
   `T x H` directly.
3. **Amenable fibres.** With `fpbs-amenable-wq-normal-pu-is-relative-pc`
   (`N` is normal, hence wq-normal), `p_h = p_c(N;G) = p_u(G)` when `H_grp`
   is amenable. For nonamenable `H_grp`, `p_h = p_c(N;G)`, which can be
   strictly below `p_u`.
4. **The Kesten step of Hutchcroft--Pan is a heaviness statement.** The
   return step (HP Lemma 2.8) that fails for nonamenable `H` in the wave-12
   attempt would give `p_c(N;G) <= p_t`. By the Theorem this is `p_h <= p_t`:
   heavy clusters must appear as soon as the half-tilted susceptibility
   diverges. So any repair of that step is a proof of `p_t = p_h` on
   `T x H`, i.e. an answer to the analogue of Hutchcroft's Question Q2(1)
   for that `H`.

The Theorem does not advance `fpbs-benjamini-schramm-universal` directly:
`T x H` already has `p_c < p_u` by Hutchcroft. Its value is that the one open
identity left on tree products is an existing named question, and that the
search for a counterexample to Claim E reduces to separating `p_t` from `p_h`.

## Attempts

- **Proving `p_t = p_h` on `T x H` for nonamenable `H` (not achieved).**
  Mean-field heuristic. A branching random walk with backtracking along the
  tree factor has fibre-occupation threshold and half-tilted threshold both
  at `m * 2 sqrt(k-1) = 1`, because `A g = 2 sqrt(k-1) g` for the tree
  adjacency `A` and `g = Delta^(1/2)`. So mean-field comparison cannot
  separate `p_t` from `p_h`, and any separation needs correlated
  fibre-to-fibre copying. No rigorous inequality in either direction beyond
  `p_t <= p_h` was obtained.
