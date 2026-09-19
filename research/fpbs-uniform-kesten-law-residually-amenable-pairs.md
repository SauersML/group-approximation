---
rg: 2
id: fpbs-uniform-kesten-law-residually-amenable-pairs
kind: claim
title: The percolation Kesten margin along a residually amenable normal subgroup is bounded below by a function of the number of generators and the quotient spectral gap alone
distinct_from:
  fpbs-percolation-kesten-normal-gap: that is the qualitative gap along every normal subgroup with nonamenable quotient; this asks for a margin delta(k,eta) uniform over all k-marked pairs with rho_Q at most 1-eta, but only along residually amenable normal subgroups.
  fpbs-uniform-l2-gap-marked-groups: that is a uniform operator bound on all of X_(k,eta) and implies this statement; this is the weaker relative-susceptibility consequence, a necessary condition that can be refuted without touching operator norms.
  fpbs-kesten-margin-collapses-near-lamplighter: that proves margins tend to 0 when rho_Q tends to 1; this asks for a positive margin whenever rho_Q stays at most 1-eta, which the lamplighter data satisfy.
  fpbs-l2-gap-transfers-to-kesten-normal-gap: that proves this statement for pairs of girth at least L(eta), and proves it follows from the uniform l2 conjecture; this is the statement for all residually amenable pairs.
---

**OPEN.** For every `k >= 2` and `eta in (0,1)` there are `M < infinity`
and `delta > 0` with the following property. Let:
- `(Gamma; s_1,...,s_k)` be a `k`-marked group with simple Cayley graph `G`;
- `N ◁ Gamma` be residually amenable in `Gamma`, as defined in
  `fpbs-l2-gap-transfers-to-kesten-normal-gap`, for example residually
  solvable;
- `rho_Q <= 1 - eta` for `Q = Gamma/N`.

Then

```text
chi^N_(p_c(G)+delta)(G) <= M,     in particular   p_c(N;G) >= p_c(G) + delta.
```

**Where it sits.**
- *Necessary for the uniform-l2 route.* It follows from
  `fpbs-uniform-l2-gap-marked-groups` via the route
  `fpbs-uniform-kesten-law-from-uniform-l2`. So a refutation, meaning a family
  of residually amenable pairs with `rho_Q <= 1 - eta` and margins tending to
  `0`, refutes the uniform-l2 route to `fpbs-benjamini-schramm-universal`.
  Restricted to pairs with `w = e` in `Gamma`, it follows from the cylinder
  `fpbs-uniform-l2-gap-short-relator-cylinders` at `(k,eta,w)`.
- *Proved where it is known.*
  - At girth at least `L(eta)`, with `delta = eta/(4(2k-1))` and
    `M = 1 + 3/eta^2` (Corollary A of
    `fpbs-l2-gap-transfers-to-kesten-normal-gap`). This includes every normal
    subgroup of `F_k`.
  - Qualitatively, on tree products (`fpbs-tree-products-schreier-kesten-gap-iff-not-co-amenable`).
  - Qualitatively, on complete-block free products
    (`fpbs-complete-block-free-products-satisfy-identity-e`).

  No uniformity in `eta` has been checked on these last two classes.
- *What it gives.* It implies the qualitative Kesten normal gap for every
  residually amenable `N` with nonamenable quotient: take
  `eta = 1 - rho_Q > 0`. By `fpbs-relative-gap-along-any-subgroup-separates`,
  this gives `p_c < p_u` on every Cayley graph of a group with an infinite
  residually amenable normal subgroup of nonamenable quotient. Examples are
  `H x K` with `K` infinite residually solvable and `H` nonamenable (take
  `N = K`), and every nonamenable residually solvable group with an infinite
  normal subgroup of nonamenable quotient.

**Test cases (where to look for a refutation).** Pairs whose quotient is
fixed and nonamenable, while the group `Gamma` moves so that `p_c(Gamma)`
changes. For example, markings of `F_m x Z^r` and of `F_m x A` for amenable
`A`, with `N` the amenable factor and mixed generators. In such cases:
- `rho_Q` stays bounded away from `1`;
- `N` is amenable, so Lemma 1 of
  `fpbs-l2-gap-transfers-to-kesten-normal-gap-proof` gives
  `chi^N <= ||T^Gamma||`, and the target there is implied by a uniform
  operator bound along the family;
- the factor-of-iid construction in Theorem 6 of
  `research/artifacts/fpbs/exploration.md` is the known source of trouble
  for operator control on `Gamma x Z`.
