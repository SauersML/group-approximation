---
rg: 2
id: permutational-boone-higman-conjecture
kind: claim
title: Every finitely generated group with solvable word problem embeds in a finitely presented group with a type (A) action
root: true
distinct_from:
  boone-higman-conjecture: that asks for an embedding in some finitely presented simple group; this asks for an embedding in a finitely presented group with a faithful type (A) action, which is formally stronger by Zaremsky's Corollary B, and equivalence of the two is open.
  type-a-action-gives-boone-higman-for-subgroups: that is the theorem turning one type (A) actor into simple envelopes for its subgroups; this is the open conjecture that every decidable group sits inside some such actor.
  boone-higman-type-a-class-closed-under-finite-extensions: that records permanence of the class this conjecture quantifies over; this asserts that the class contains every decidable finitely generated group.
artifacts:
  - research/artifacts/bh-type-a-permanence-2026-09-12.md
---

**OPEN.** This is the universality target of the twisted Brin--Thompson route to
`boone-higman-conjecture`.

**Statement** (Belk--Fournier-Facio--Hyde--Zaremsky, arXiv:2503.21882v2, read
through a summarizing fetch): "Every finitely generated group with solvable word
problem embeds in a group admitting an action of type (A)."

Here an action of Gamma on S is of type (A) when:
- it is faithful;
- Gamma is finitely presented;
- every point stabilizer is finitely generated;
- there are finitely many orbits of pairs.

**Relation to Boone--Higman.**
- **It implies BH.** By Zaremsky, arXiv:2405.18354, Corollary B
  (`type-a-action-gives-boone-higman-for-subgroups`), the twisted Brin--Thompson
  group of such an actor is finitely presented and simple. Route:
  `boone-higman-via-permutational-boone-higman`.
- **The converse is open.** BFFHZ call it "a fundamental question" whether BH
  and PBH are equivalent. Fournier-Facio--Wu--Zaremsky, arXiv:2603.24687v2, call
  it "a major question whether (PBH)⇔(BH), or equivalently whether twisted
  Brin--Thompson groups are universal among finitely presented simple groups".
  BFFHZ's route question is `fp-simple-groups-embed-in-fp-simple-mif-groups`.
- **The relative version follows from BH.** FFWZ Theorem C (Theorem 5.1): "If a
  group satisfies the Boone--Higman conjecture then it satisfies the relative
  permutational Boone--Higman conjecture." Their Question 5.9 asks whether
  relPBH implies PBH.

**Known positive inputs.**
- **Aut(F_n):** BFFHZ Theorem A (`aut-free-groups-satisfy-permutational-boone-higman`).
- **Permanence:** the class is closed under commensurability and direct
  products (Zaremsky Proposition 5.6;
  `boone-higman-type-a-class-closed-under-finite-extensions`), and under free
  products (BFFHZ Corollary F).
- **Full Cantor groups:** a finitely presented full Cantor group containing
  standard V carries a type (A) action
  (`fp-full-binary-cantor-groups-have-type-a-actions`).

## Attempts

- **Finite bi-index core.** `boone-higman-via-finite-bi-index-envelope` builds
  exactly a type (A) action of the Chatterji--Kassabov cover on cosets of the
  simple core. Its open clause is `ck-envelope-simple-core-has-finite-bi-index`.
- **Automorphism action image.** The universal computable-core upgrade in
  `bffhz-action-image-is-finitely-presented` is refuted by
  `bffhz-computable-core-fp-upgrade-is-false`. BFFHZ's own question assumes a
  finitely presented core.
- **Shell and shift envelopes.** `boone-higman-via-fp-shell-envelopes` and its
  siblings leave finite presentation of the envelope open. A finitely presented
  full Cantor envelope containing V would supply a type (A) action.
- **Necessity.** `complexity-bounded-host-classes-are-not-universal` shows that
  the actors for all inputs cannot share a recursive bound on word-problem
  complexity. Any universal construction must consume the input's algorithm.
