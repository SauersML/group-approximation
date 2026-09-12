---
rg: 2
id: stw01-monotone-complete-ii1-awstar-factors-are-w-star
kind: claim
title: No monotone complete type II_1 AW*-factor is wild
distinct_from:
  stw01-ii1-awstar-factors-are-monotone-complete: that asks whether every II_1 AW*-factor is monotone complete; this asks whether monotone completeness already forces a II_1 factor to be W*, i.e. whether wild II_1 factors are impossible.
  stw01-quasitrace-crux-is-awstar-factor-w-star: that is the W*-corner question for every II_1 AW*-factor; this is its restriction to the monotone complete ones.
artifacts:
  - research/artifacts/stw01-host-survey-2026-09-12.md
---

Every monotone complete type `II_1` AW*-factor is a W*-factor. Equivalently, no
wild factor (monotone complete, not W*) is of type `II_1`.

By Gow arXiv:2601.04431v2, Corollary 4.10, a type `II_1` AW*-factor is a W*-factor
iff it is a *-homomorphic retract of its bidual. So this claim is exactly the type
`II_1` factor case of Gow Question 6.3 ("is every monotone complete C*-algebra a
retract of its bidual?"). Gow Proposition 6.2 gives the easy converse: a retract of
the bidual is monotone complete. An AW*-algebra with a separating family of states completely
additive on projections is W* (Gow Corollary 3.10). Gow's introduction quotes
Wright (J. London Math. Soc. 1975/76) for a faithful state, not assumed normal, on
a type `II_1` AW*-factor. That hypothesis was not checked against the primary
source.

Context: the known non-W* AW*-factors (Dyer 1970, Takenouchi 1970, Hamana 2001,
Saitô–Wright generic dynamics) are all type III, and no non-W* type II AW*-factor
is known.

## Attempts

- **Transfer the type III wild constructions to type `II_1`.** The Dyer and
  Takenouchi factors fail to be W* because they admit no normal states. A type
  `II_1` AW*-factor always carries its faithful, normal-on-projections quasitrace,
  so that mechanism has no `II_1` analogue. Dies.
- **Build the retraction `A** -> A` from monotone completeness** (converse of Gow
  Proposition 6.2). In the commutative case the retraction comes from injectivity
  of Stonean `C(X)` among commutative C*-algebras (Hadwin–Paulsen). No
  noncommutative injectivity for *-homomorphisms is available. Dies.
- **Faithful-state route** (Wright 1975). Monotone completeness produces no linear
  functional, and the only canonical functional is the quasitrace, whose linearity
  is Problem I. Dies at existence.
