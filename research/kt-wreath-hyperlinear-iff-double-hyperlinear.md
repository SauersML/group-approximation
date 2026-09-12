---
rg: 2
id: kt-wreath-hyperlinear-iff-double-hyperlinear
kind: claim
title: The Kun--Thom binary wreath is hyperlinear iff the Kun--Thom double is, iff the pair is relatively embeddable
distinct_from:
  kt-q2-double-hyperlinear-iff-relative-embeddable: that records the double-to-relative-embeddability half for the same pair; this adds the wreath group itself as a third equivalent and is the node the wreath-construction goal points at, so the two lanes read as one problem.
  binary-free-and-ordinary-coset-wreaths-share-hyperlinearity: that is the general theorem for every countable pair; this is its instantiation at the specific Kun--Thom Theorem E pair, recording the consequence the general node does not name.
  hyperlinear-wreath-model: that asks to CONSTRUCT hyperlinear microstates of the wreath; this is the unconditional equivalence that says what such a construction is worth and where else it may be sought.
artifacts:
  - research/artifacts/kt-wreath-double-re-unification-2026-09-11.md
---

**ESTABLISHED.**  Fix the Kun--Thom Theorem E pair
`Gamma = EL_r(F_q[x_1,...,x_d]) < G = EL_r(F_q[x_1^(±1),...,x_d^(±1)]) rtimes SL_d(Z)`
(`kun-thom-nonsofic-wreath`).  Then the following are equivalent.

1. The Kun--Thom binary wreath
   `W = (direct_sum_(G/Gamma) Z/2Z) rtimes G` is hyperlinear.
2. The Kun--Thom double `D = G *_Gamma G` is hyperlinear.
3. The inclusion `L(Gamma) <= L(G)` is relatively embeddable over the scalar
   algebra `C` (`RE/C`, Gao arXiv:2012.07940, Definition 2.2).

Equivalently, the centralizer HNN group `G *_Gamma (Gamma x Z)`, the free
binary coset wreath `G *_Gamma (Gamma x Z/2Z)`, and the Gaussian crossed
product `L^infinity(R^(G/Gamma), gamma) rtimes G` share this one status.

This is the instantiation at `(A,C) = (G,Gamma)` of the general equivalence
`binary-free-and-ordinary-coset-wreaths-share-hyperlinearity`, whose object
(1) is verbatim the ordinary binary coset wreath and whose object (4) is the
symmetric double.  The double-to-relative-embeddability half is separately
established for this exact pair as
`kt-q2-double-hyperlinear-iff-relative-embeddable`.

**Why record it.**  The wreath is the group Kun--Thom prove nonsofic
(`kun-thom-nonsofic-wreath`, Theorem A) and the double is the group whose
reduced C*-algebra the separation route
`hyperlinear-nonsofic-from-kt-reduced-cstar-mf` attacks; this equivalence
makes those two lanes one problem, so every wreath-side obstruction
(`kt-wreath-relative-canonical-actor-exactification`,
`kt-two-positive-compressors-generate-full-obstruction`) and every double-side
input (`kt-double-reduced-cstar-is-mf`, `kt-q2-double-reduced-cstar-has-unique-trace`)
constrains the same object.  The shared object is `RE/C` for a property-(T)
base: `Gamma` and `G` are Kazhdan, so this is an instance of the
Gao--Junge open amalgamated-free-product problem over a non-hyperfinite base,
and no permanence theorem in the literature resolves it (the audit artifact
lists them).  This is why both branches of the fork machine
(`kun-thom-nonsofic-wreath`: hyperlinear gives Pestov 3.4 separation,
nonhyperlinear gives `non-hyperlinear-group`) remain open.

The equivalence does not decide any of (1)--(3); it only proves they stand or
fall together.

DERIVATION
kt-wreath-hyperlinear-iff-double-proof
