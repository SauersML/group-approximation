---
rg: 2
id: normal-fibre-galois-games-round-linearly-over-m-groups
kind: claim
title: For normal K and monomial certificates (every nilpotent G), SDP 1-eps gives L meeting K trivially with mu(G minus L) <= 3 eps log_q k/(1 - cos(2 pi/m))
distinct_from:
  galois-games-round-through-free-subgroups: that rounds through kernels of the irreducibles and pays their dimensions; this rounds through kernels of the inducing linear characters and pays nothing for dimension.
  elementary-abelian-galois-games-round-with-linear-loss: that is the case G = F_p^N, proved with Bochner and Fourier inversion; this covers every nilpotent group and every M-group with normal K.
  free-subgroup-rounding-fails-for-non-normal-fibres: that shows the free-subgroup form fails for non-normal K; this proves it for normal K over M-groups.
artifacts:
  - research/artifacts/ugc-rounding-normal-fibres-2026-09-13.md
---

**ESTABLISHED.** Notation of `galois-unique-game-value-is-transversal-expansion`.
Let `G` be finite of exponent `m`, `K` normal of order `k`, `q` the least prime
dividing `k`, and `mu` symmetric and conjugation-invariant. Suppose
`SDP Gal(G,K,mu) >= 1 - eps`, or more generally that some admissible `phi` has
`sum mu phi >= 1 - eps`. Suppose every irreducible with
`lambda_rho >= 1 - 3 eps` is monomial. This holds whenever `G` is an M-group,
and every nilpotent group, in particular every `p`-group, is one.

Then there are `t <= log_q k` subgroups, each a conjugate of the kernel of a
linear character of a subgroup, whose intersection `L` has `L cap K = {e}` and

```text
mu(G \ L) <= 3 eps log_q k / (1 - cos(2 pi/m)).
```

So `L` acts freely on `G/K`, and `val >= 1 - 3 eps log_q k/(1 - cos(2 pi/m))`.

The key identity: if `rho = Ind_H^G theta` and `mu` is conjugation-invariant,
then `chi_rho(mu)/d_rho = sum_(h in H) mu(h) theta(h)`. This is the `mu`-value of
the single basis vector `e_H`, and Markov on the `m`-th roots of unity gives
`mu(G \ ker theta) <= (1 - lambda_rho)/(1 - cos(2 pi/m))`. Since
`ker rho` is the intersection of the conjugates of `ker theta`, a halving chain
inside `K` needs at most `log_q k` of them.

This is the abelian constant of Corollary 9 in
`galois-games-round-through-free-subgroups`, now over every nilpotent group,
with no dimension factor. It resolves the normal-`K` sharper form of
`free-subgroup-rounding-is-universal-at-bounded-exponent` over M-groups:
large irreducibles of `p`-groups never obstruct subgroup rounding, because
they are monomial. Khot--Vishnoi shows that the `log k` factor is necessary,
and the odd cycle `Z_(2n)` shows that some dependence on `m` is necessary.

It constrains symmetric integrality-gap constructions only, and neither proves
nor refutes `unique-games-conjecture`.
