---
rg: 2
id: lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap-proof
kind: route
title: Transfer perfect qc and qa strategies along the hereditary equivalence of syncBCS and the CFI isomorphism game
target: lcs-tracial-nonru-gap-gives-qc-qa-cfi-graph-gap
requires: []
artifacts:
  - research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md
---

**Sources.**

BCEHPSW = Brannan, Chirvasitu, Eifler, Harris, Paulsen, Su, Wasilewski,
arXiv:1812.11474v2, read at source.

- **(H1)** Theorem 2.1(3),(4).  A synchronous game has a perfect `qa`-strategy
  iff its game algebra has a unital *-homomorphism into `R^U`.  It has a
  perfect `qc`-strategy iff its game algebra has a unital *-homomorphism into
  a unital C*-algebra with a faithful trace.
- **(H2)** Definitions 5.4 and 5.5 and Theorem 5.6.  `syncBCS(A,b)` and
  `Iso(G_(A,b), G_(A,0))` are hereditarily *-equivalent.
- **(H3)** Proposition 5.3.  Hereditarily *-equivalent synchronous games have
  perfect `t`-strategies simultaneously, for `t in {loc, q, qa, qc, C^*}`.

AMRSSV = Atserias, Mančinska, Roberson, Šámal, Severini, Varvitsiotis,
*Quantum and non-signalling graph isomorphisms*, arXiv:1611.09837, read at
source through text extraction.

- **(A1)** §6.1: the graphs `G_F`, `G_(F_0)` of a linear system and its
  homogenization.  Theorem 6.3: `F` is quantum satisfiable iff
  `G_F ≅_q G_(F_0)`.
- **(A2)** Theorem 6.5: the BCS game for `F` has a perfect quantum commuting
  strategy iff `G_F ≅_qc G_(F_0)`.  This is the `qc` transfer below, and it is
  due to AMRSSV.  BCEHPSW (H2)--(H3) give it again and add the `qa` case.

Paddock--Slofstra, arXiv:2310.07901v2, read at source.

- **(P1)** p. 2.  The synchronous algebra of the synchronous BCS game is
  isomorphic to the BCS algebra.  For linear systems this is due to
  Kim--Paulsen--Schafhauser and Goldberg; their papers were not re-read here.
- **(P2)** Definition 3.12(iii),(iv).  A system is `R^U`-satisfiable iff there
  is a *-representation `A(B) -> R^U`, and tracially satisfiable iff `A(B)` has
  a tracial state.

**Tracial state iff perfect qc-strategy.**  A tracial state `tau` on `A(B)`
gives the GNS algebra `pi_tau(A(B))''`, whose trace is faithful.  So there is a
unital *-homomorphism into a C*-algebra with a faithful trace.  Conversely,
such a homomorphism pulls the faithful trace back to a tracial state.  By
(P1) and (H1), `A(B)` has a tracial state iff `syncBCS(A,b)` has a perfect
`qc`-strategy.

**R^U-satisfiable iff perfect qa-strategy.**  By (P1), (P2) and (H1),
`A(B)` has a *-homomorphism into `R^U` iff `syncBCS(A,b)` has a perfect
`qa`-strategy.

**Transfer.**  By (H2) and (H3) with `t = qc` and with `t = qa`,
`syncBCS(A,b)` has a perfect `qc`-strategy iff `Iso(G_(A,b), G_(A,0))` does,
and the same holds for `qa`.  Combining the three equivalences:

- `A(B)` is tracially satisfiable iff `G_(A,b) ≅_qc G_(A,0)`;
- `A(B)` is `R^U`-satisfiable iff `G_(A,b) ≅_qa G_(A,0)`.

The claimed equivalence follows.
