---
rg: 2
id: unfolding-tensor-clauses-returns-the-original-gap
kind: claim
title: Unfolding each amplified tensor clause into the average of its factors returns exactly the input ground energy
artifacts:
  - research/artifacts/qpcp-dinur-iteration-architecture-2026-09-11.md
distinct_from:
  ordinary-gap-amplification-grows-locality: that says known amplifiers buy gap by growing locality; this says the most natural way to buy locality back, splitting amplified clauses into their factors, gives the whole gain back.
  locality-reduction-with-amplifier-independent-loss: that is the open reducer demanded by the Dinur route; this proves one natural candidate reducer cannot meet its t-independent loss clause.
---

**ESTABLISHED (ordinary proof).** Let `H=sum_chi w_chi H_chi` be layered as in
BMVZ Definition 1.6, and let `H^(t)` be its derandomised amplification over the
length-`t` walks `F_chi` of `d`-regular graphs, each walk with equal weight.
Define

```text
U_t(H) = sum_chi w_chi E_(f in F_chi) (1/t) sum_(j in [t]) (Pi^chi_(f(j)))_(copy j).
```

1. **(UF1)** `U_t(H) <= H^(t)`. For each walk the factors sit on distinct copies
   and commute, and `I - tensor_j (I-P_j)` dominates every `P_j`, hence their
   average.
2. **(UF2)** `U_t(H)=(1/t) sum_(j in [t]) H_(copy j)`. The uniform distribution
   is stationary for the walk on a regular graph, so every coordinate `f(j)` of
   a uniform walk is uniform on `[m_chi]`.
3. **(UF3)** `lambda_min(U_t(H))=lambda_min(H)`. `U_t(H)` is layered with the
   same weights and the same locality `k`, on `t` copies.
4. **(UF4) Loss.** Suppose a reducer outputs `U_(2t)(H)` from `H^(2t)` and
   satisfies (RED1) of `locality-reduction-with-amplifier-independent-loss`
   with constant `c`. Then for every `H` in the regime where BMVZ soundness
   (6.66) is the binding term,
   `c<=lambda_min(H)/lambda_min(H^(2t))<=sqrt(log t/t)/eta`, with
   `eta=1/(20max{1+C_mu,omega_min})`. The one-qubit projector-pair family of
   `qubit-pairs-have-half-gap-and-unbounded-rounder-cost` is layered with two
   commuting layers, locality one, `omega_min=2`, and ground energy
   `1/(N^2+1)`. It lies in every class `L(k_0,g_0,omega_0)` of that claim and
   enters the binding regime for large `N`. So no `c>0` independent of `t`
   works for the unfolding.

**Reading.** Amplify-then-unfold is the identity on ground energy. It keeps
completeness (UF1) and locality, and it undoes the amplification exactly. A
reducer meeting the `t`-independent clause must use the tensor structure of
the amplified clauses, not just their factors.
