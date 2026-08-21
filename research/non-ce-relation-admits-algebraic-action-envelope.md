---
rg: 2
id: non-ce-relation-admits-algebraic-action-envelope
kind: claim
title: The non-CE relation algebra embeds into one algebraic compact abelian crossed product
distinct_from:
  non-ce-property-t-equivalence-relation-exists: that establishes existence of the non-CE relation factor by IRS and property-T envelope; this demands a second, ALGEBRAIC envelope — compact abelian base, automorphic action, Haar measure — so that Pontryagin duality applies.
  algebraic-envelope-principle: that is the established compiler consuming this hole; this is the construction obligation itself.
  kun-thom-clifford-crossed-product-ce: that asks whether one specific Clifford crossed product is CE; this asks to place a KNOWN non-CE algebra inside some algebraic crossed product, with full freedom in choosing the base and the acting group.
---

Construct a compact second-countable abelian group `K`, a countable
group `Lambda` acting on `K` by continuous automorphisms, and a
trace-preserving embedding

```text
L(R)  ->  L^infinity(K, Haar) rtimes Lambda,               (AAE1)
```

where `L(R)` is the non-Connes-embeddable relation factor of
`non-ce-property-t-equivalence-relation-exists`.  Any non-CE tracial
algebra in place of `L(R)` is equally acceptable.  By
`algebraic-envelope-principle` this alone produces the explicit
non-hyperlinear group `hat K rtimes Lambda`.

## Attempts

- **Haar linear subshift design.**  The natural candidates are closed
  shift-invariant subgroups `K <= (F_p^m)^Lambda` cut out by finitely
  many linear local rules: the action is algebraic by construction,
  Haar is the natural measure, and the dual `hat K` is a finitely
  generated `F_p[Lambda]`-module, so `hat K rtimes Lambda` is finitely
  generated and recursively presented.  The decisive design constraint
  is to make the non-CE witness's invariant measure HAAR, not merely
  shift-invariant: for non-Haar measures the duality `(AEP1)` fails and
  the compiler does not apply.  This is a new reading of the existing
  finite-field/LCS gadget library: as measure-algebraic processes, not
  as robust matrix decoders — no finite-dimensional soundness theorem
  is needed at the compiler stage.
- **Freeness is a convenience, not an obstacle.**  If a candidate
  action is not essentially free, tensor with an algebraic Bernoulli
  shift `(F_p)^Lambda`: products of algebraic actions are algebraic,
  freeness is restored, and an embedding `(AAE1)` into the smaller
  crossed product persists into the larger one.  The subtle point is
  to secure the inclusion at the crossed-product level first; a non-CE
  QUOTIENT of a crossed product proves nothing here.
- **Where the obvious attempt dies.**  The property-T relation
  envelope behind the established input is a wreath-like construction
  on a p.m.p. base that is not visibly algebraic; simply declaring the
  base to be a group rotation fails because the envelope's measure is
  built from the IRS, and nothing forces it to be Haar on any group
  structure.  The genuine work is either (a) re-run the envelope
  construction inside the category of algebraic actions — the
  wreath-like extension of an algebraic action by a finite-field
  module IS algebraic, so the question is whether the IRS trace can be
  realized on an algebraic base — or (b) design a new non-CE witness
  natively as a Haar linear subshift, using the correlation-to-module
  dictionary.
- **Source-structure triage (2026-08-21, from arXiv:2502.06697v2).**
  The witness's acting group is `*_Q Z_2^m x Z_2` — a free product of
  finite abelian `2`-groups, hence VIRTUALLY FREE: excellent for
  subshift design (tree-shifts over virtually free groups have strong
  effective theory), and `hat K rtimes Lambda` would be (finitely
  generated module)-by-(virtually free), certainly recursively
  presented.  The IRS trace is `tau_H` on the free group with
  `L(Gamma/H) = tau_H(Gamma)''` non-CE because a tailored game has
  `omega_IRS > omega*` (TailoredMIP* = RE); the base pmp space is the
  abstract GNS/stabilizer space, NOT a group.  The naive
  algebraization fails at a precise point: `Sub(Gamma)` inside
  `{0,1}^Gamma` is a closed shift-invariant SUBSET but not a
  subGROUP — subgroup indicators are not closed under addition — so
  the stabilizer realization is a subshift, never a linear subshift,
  and no Haar structure comes for free.
- **Sharpened branch (a): algebraic completeness for one tailored
  game.**  In `L^infinity(K) rtimes Lambda` for a Haar linear subshift
  `K <= (F_2^m)^Lambda`, order-two dual characters give native
  `±1`-observables, and correlations of character/group words are
  normalized solution counts of linear systems over the
  `F_2[Lambda]`-module `hat K`: Haar-module strategies realize exactly
  LCS-type correlations.  Branch (a) therefore reduces to: can the
  COMPLETENESS (honest) strategies of one tailored halting game with
  `omega_IRS > omega*` be taken in module/Haar form — i.e., is
  `omega_alg > omega*` for some such game?  A positive answer places
  the non-amenable trace on `L(hat K rtimes Lambda)` and closes this
  hole outright; a negative structural answer (module strategies
  provably amenable-dominated) kills branch (a) and concentrates all
  effort on branch (b).  This meshes with the graph's existing
  LCS/BCS compiler lane, but consumes only completeness-side
  structure — no robust finite-dimensional soundness is needed.
- **Falsification test.**  Fourier positivity is a real constraint:
  coefficients of Haar algebraic processes satisfy character-positivity
  identities that a general p.m.p. correlation need not.  Check the
  imported witness's correlations against these identities first; a
  clean violation on every algebraic re-realization would kill route
  (a) and redirect all effort to (b).
