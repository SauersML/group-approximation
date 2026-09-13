---
rg: 2
id: fg-simple-weakly-sofic-groups-are-finite-field-linear-sofic
kind: claim
title: Every finitely generated simple weakly sofic group is linear sofic over finite fields
distinct_from:
  fp-simple-weak-soficity-is-finite-field-linear-soficity: that proves this for finitely presented simple groups, where the PSL dichotomy uses a finite presentation; this asks it for finitely generated simple groups, the class on which the rigidity claim and its Kazhdan envelope route are stated.
  fg-simple-weakly-sofic-groups-are-sofic: that is the rigidity claim, which implies this one; with this claim, the rigidity claim becomes the statement that finitely generated simple groups linear sofic over finite fields are sofic.
---

**ESTABLISHED (2026-09-13, lane `ex3-weak-sofic-fg-dichotomy`, unreviewed)** by two independent routes:
- `fg-simple-weak-sofic-linear-sofic-via-nst-conjugacy`: the proof of Nikolov--Schneider--Thom Theorem 4 (projective-rank
  ultraproducts), then the adjoint representation;
- `fg-simple-weak-sofic-linear-sofic-via-near-scalar-covering`: only the statement of NST Theorem 4, plus a compactness
  collapse and the covering argument of the PSL dichotomy.

Derivations: `research/artifacts/fg-simple-weak-soficity-finite-field-linear-2026-09-13.md`.

Let `G` be a finitely generated simple group that is weakly sofic. Then `G` embeds in a rank-metric ultraproduct of groups
`GL_(n_i)(F_(q_i))` (definition on `simple-group-psl-width-is-finite-field-linear-soficity`). Since the converse inclusion
always holds, **a finitely generated simple group is weakly sofic iff it is linear sofic over finite fields.**

**Payoff.**
- `fg-simple-weakly-sofic-groups-are-sofic` is equivalent to: *every finitely generated simple group that is linear sofic
  over finite fields is sofic*.
- The Kazhdan envelope route `non-weakly-sofic-group-from-simple-weak-sofic-rigidity` needs only that statement, for the
  simple Kazhdan envelope of the Kun--Thom wreath. That envelope is weakly sofic iff it is linear sofic over finite fields.
- With Schupp's embedding, some group is not weakly sofic iff some group is not linear sofic over finite fields
  (artifact, Section 4).

**Credit.** The reduction to groups `PSL_n(q)` with the projective rank length is due to Nikolov--Schneider--Thom
(arXiv:1703.06092v2, proof of Theorem 4). The new part is the adjoint step, the observation that it closes the finitely
generated case, and the direct second proof. The novelty check was bounded to NST pp. 1--5, 10--14, 19--20 and
Arzhantseva--Paunescu pp. 1--3, with no web search.

## History: the near-scalar horn is empty

- **Before 2026-09-13 (lane `ex2-weak-sofic-bounded-factors`).** The composite
  `G -> prod_U (PSL_(n_i)(q_i), l^pr)`, built from NST Theorem 4's *statement* with arbitrary lengths, was injective or
  trivial. The trivial case was left open: tuples within rank `o(n_i)` of the scalars, with `n_i -> infinity`.
- **Closed.** Two arguments do it.
  - *First.* The proof of NST Theorem 4 already lands in the projective-rank ultraproduct, so the trivial case never
    arises.
  - *Second.* In the trivial case, Sections 5.1--5.5 of `simple-group-psl-width-is-finite-field-linear-soficity-proof`
    run over a finite relation set `R'`, with collapse constant supplied by compactness (artifact 3.0). They bound every
    generator's length by boundedly many relation lengths, which contradicts separation.
- **Why the finitely presented proof seemed not to transfer.** The obstruction was the *width formulation*, one finite
  relator set normally generating the kernel. Linear soficity needs only finitely many relations of a fixed template,
  and 3.0 supplies them.
