---
rg: 2
id: simple-torsion-non-mf-iff-trivial-mf-characters
kind: claim
title: A simple torsion-marked group has full MF radical iff its only MF-character is trivial
artifacts:
  - notes/PROPERTY_T_FREE_MF_ATTEMPT_2026-08-26.md
distinct_from:
  simple-torsion-groups-have-a-macroscopic-mf-dichotomy: that produces a faithful Hilbert--Schmidt-separated operator-norm model from a surviving mark; this packages its consequence as a character criterion.
  hyperlinear-trace-not-mf-trace: that separates two trace classes on one C-star algebra by an explicit example; this is an equivalence between a group-level radical and absence of faithful MF characters.
  mf-implies-hyperlinear: that compares approximation notions for arbitrary groups; this is the exact equivalence for simple torsion-marked groups.
---

Call a character `chi` of a countable group `G` an **MF character** when
there are operator-norm asymptotic unitary representations
`sigma_n:G->U(d_n)` such that `tr_(d_n)(sigma_n(g))->chi(g)` for every `g`.
Let `G` be a nontrivial finitely generated simple group containing a
nonidentity element of finite order.  Then the following are equivalent:

1. `Rad_MF(G)=G`;
2. every MF character of `G` is the trivial character;
3. no MF character of `G` is faithful.

This applies directly to simple elementary-group targets.  It is not used to
assert simplicity of the literal Steinberg central cover; that target is
handled by the separate torsion-normal-generator character criterion.

The reformulation does not solve any Leavitt endpoint.  A proof using only
normalized Hilbert--Schmidt multiplicativity and excluding the regular
character would prove nonhyperlinearity.  A genuinely MF-specific proof must
consume operator-norm/corona structure.

No Property `(T)`, stability theorem, or literature input is used.

DERIVATION
simple-torsion-non-mf-iff-trivial-mf-characters-proof
