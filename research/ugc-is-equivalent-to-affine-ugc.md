---
rg: 2
id: ugc-is-equivalent-to-affine-ugc
kind: claim
title: The Unique Games Conjecture is equivalent to its restriction to bipartite shift games x_v = x_u + b over Z_q, and equally to shift games over any fixed abelian group family of order q such as F_2^N (KKMO 2007), but the equivalence changes the constraint graph
distinct_from:
  rich-2to1-conjecture-is-equivalent-to-ugc: that is Braverman--Khot--Minzer's equivalence with a 2-to-1 variant; this is the older KKMO equivalence with the affine (linear-shift) subclass of unique games.
  affine-ug-easy-on-globally-hypercontractive-graphs: that is an algorithm for affine UG on fixed host families; this says affine UG carries the full hardness of UGC, but only on hosts the KKMO reduction chooses.
  affine-ug-easy-on-certifiably-hypercontractive-graphs: that is the BBKSS algorithm on certified small-set expanders; this is a hardness equivalence with no host restriction.
  elementary-abelian-galois-games-round-with-linear-loss: that rounds special symmetric quotient instances over F_p^N; this says general F_2^N-shift instances already carry UGC, so the Galois rounding cannot extend to all of them unless UGC fails.
---

**ESTABLISHED, BY CITATION.** Khot, Kindler, Mossel and O'Donnell, *Optimal
Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?*, SIAM J.
Comput. 37(1) (2007). Route: `ugc-is-equivalent-to-affine-ugc-citation`.

**Statement.** The following are equivalent.

1. The Unique Games Conjecture (`unique-games-conjecture`).
2. For every `eps > 0` and every `q` large enough in terms of `eps`,
   Gap-UG[`1 - eps`, `8 (1/q)^(eps/(2-eps))`] is NP-hard on **bipartite** unique
   games with alphabet `Z_q` whose every constraint is a shift
   `x_v = x_u + b_e`, which is Affine-UG in the sense of Bafna--Minzer
   Definition 1.4.
3. The same as (2), with `Z_q` replaced by any fixed abelian group `A_q` of
   order `q`, for example `A_q = F_2^N` with `q = 2^N`, and shifts
   `x_v = x_u + b_e` taken in `A_q`.

(2) and (3) each imply (1) trivially, because they are subclasses of unique
games with alphabet `q` and their soundness tends to `0` as `q` grows. KKMO
Theorem 12 and Corollary 13, under UGC, give NP-hardness for non-bipartite
instances `x_i - x_j = c`, with soundness `(1/q)^(eps/(2-eps))`. Their remark
on page 27 says the results hold over every fixed abelian group of order `q`.
The route removes loops with fresh variables (soundness `+ 1/q`) and passes to
the bipartite double cover (soundness `x 4`), for a total factor of at most `8`. KKMO Corollary 15 states the same equivalence for bipartite
Unique Label Cover with a factor `2`.

**Why the host matters.** The equivalence is not host-preserving. The KKMO
reduction composes the source label-cover instance with a noisy `q`-ary long
code, so the output constraint graph is chosen by the reduction and not by the
source instance. Bafna--Minzer, page 4, footnote 2: "the reduction of
[KKMO07] does not preserve the topology of the graph. We are therefore not able
to translate our results directly to the class of general UG". So:

* Hardness can always be carried by shift instances, but on hosts the reduction
  picks.
* An algorithm for shift instances on a fixed host family says nothing, through
  this equivalence, about general unique games on that family.
  `unique-games-reduce-to-shifts-over-their-holonomy-group` gives the
  host-preserving replacement: a gauge-invariant criterion, the holonomy group,
  for when a unique game on a fixed host *is* a shift game on that same host.

**Bearing.** With `A_q = F_2^N`, UGC is equivalent to hardness of
`F_2`-linear shift games `x_v = x_u + b_e`, `b_e in F_2^N`. These are not
cyclic for `N >= 2`, so they fall outside Bafna--Minzer Definition 1.4, and
their algorithm does not cover them even on Grassmann hosts. This is rung R2
of the ladder in `general-unique-games-easy-on-globally-hypercontractive-graphs`.

DERIVATION ugc-is-equivalent-to-affine-ugc-citation
