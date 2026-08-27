---
rg: 2
id: dellm-all-dual-presentation-has-many-unique-neighbors
kind: claim
title: The all-local-dual presentation of a DELL​M left-right Cayley code has robust unique neighbors
distinct_from:
  soundness-unique-neighbors-give-erasure-cleaning: that is an abstract implication from classical soundness and robust unique neighbors; this verifies both hypotheses for one explicit good-LTC presentation.
  positive-rate-tanner-tests-have-contextual-models: that constructs noncommuting exact local models; this is a classical common-support cleaning theorem and therefore removes only the projective/central-sign part of those models.
  collective-sheaf-cofilling-for-good-ltc: that asks for collective cofilling through the general First--Kaufman sheaf theorem; this uses the concrete four-vertex square geometry and every dual check of the fixed local tensor code.
---

Let `X=Cay^2(A;G;B)` be a TNC left-right Cayley complex with
`|A|=|B|=r`.  Its one-skeleton is `2r`-regular; assume its normalized
second eigenvalue is at most `lambda`.  Put `q=r^2`.  At each vertex `v`,
let `C_v<=F_2^(S(v))` be the fixed local tensor code, of normalized distance
at least `delta`, and define the global square code

```text
C={x in F_2^S : x|_(S(v)) in C_v for every v}.
```

Present `C` by one labelled parity row `(v,h)` for every
`h in C_v^perp`.  This is still a bounded-width, bounded-column-degree
presentation: `q` and the number of local dual words are fixed independently
of `|G|`.

For every `gamma in (0,1)` with

```text
lambda < delta(1-gamma),
alpha := delta(delta(1-gamma)-lambda),                  (DAU1)
```

every nonempty square set `U` with `|U|<alpha|S|` has at least
`gamma|U|` labelled parity rows meeting `U` in exactly one square.
Thus this concrete parity-check matrix satisfies `(SUN2)`.

If, in addition, the vertex-membership tester has classical soundness
`kappa>0`, then the same matrix satisfies `(SUN1)`: a rejecting vertex
violates at least one of its labelled dual rows, while TNC gives
`|S|=q|G|/4`, so

```text
dist_Hamming(x,C) <= (q/(4 kappa)) wt(Hx).               (DAU2)
```

Consequently the explicit DELL​M good-LTC family may be chosen with
`lambda<delta/2`; taking `gamma=1/2`, its all-local-dual presentation has
uniform common-support erasure cleaning by
`soundness-unique-neighbors-give-erasure-cleaning`.  The stronger spectral
inequality is compatible with their construction: the local code is first
fixed, and then the size `r`/outer Ramanujan member is chosen so that the
normalized Cayley eigenvalue is below any fixed positive threshold.

This settles existence of a positive-rate, linear-distance, bounded-degree
binary code satisfying the projective erasure-cleaning hypothesis.  It does
not contradict `positive-rate-tanner-tests-have-contextual-models`: common
erasure cleaning rounds central/projective parity sectors, not the genuinely
noncentral class-two local representations.

Primary source: [Dinur--Evra--Livne--Lubotzky--Mozes, Good Locally Testable
Codes, arXiv:2207.11929](https://arxiv.org/abs/2207.11929), especially the
left-right square counts, Definition 4.4, and Theorem 4.5.
