---
rg: 2
id: osin-periodic-quotient-is-non-mf
kind: claim
title: Osin's periodic quotient is a non-MF group by a mechanism disjoint from the compression
root: true
distinct_from:
  infinite-fg-bounded-exponent-groups-are-non-mf: that is the general theorem about every infinite finitely generated bounded-exponent group; this is one named group, reachable both as an instance of that theorem and by a strictly cheaper route needing a single stable implication rather than the whole restricted Burnside family.
  binary-leavitt-all-ranks-full-mf-radical: that is the established non-MF result of this repository, obtained through the Leavitt self-compression, property (T) and a Hilbert--Schmidt transport; this would be a second, independent non-MF group whose proof uses none of those.
artifacts:
  - research/artifacts/opnorm-burnside-dossier-2026-08-24.md
---

Let `Gbar = G/G^n` be the finitely generated infinite periodic group of
exponent dividing `n` supplied by
`osin-torsion-universal-theory-separator`. **Claim:** `Gbar` is not MF.

This is a program target rather than a curiosity. The repository already
owns non-MF groups, but every one of them comes from the same mechanism --
the Leavitt self-compression `tau L tau^(-1) <= L`, finite-dimensional
commutant rigidity, and transport through an ultraproduct of normalized
Hilbert--Schmidt matrix spaces. `Gbar` would be a non-MF group proved so
with **no** compression, no property `(T)`, no trace, no Hilbert--Schmidt
norm, no corner, no rank and no lamp: the only analytic input would be a
spectral gap on torsion unitaries in the original matrix norm. A second
independent mechanism is worth more than a second example.

## Attempts

1. **As an instance of the general theorem.** Route
   `osin-non-mf-from-general-bounded-exponent`: `Gbar` is infinite, finitely
   generated and of exponent dividing `n`, so
   `infinite-fg-bounded-exponent-groups-are-non-mf` applies verbatim. This
   is the expensive road -- it needs the whole restricted Burnside family of
   moduli.

2. **By one stable implication.** Route
   `non-mf-from-stable-osin-horn-separator`: it suffices to prove
   `osin-horn-separator-is-opnorm-stable`, a **single** dimension-free
   inequality attached to one fixed presentation. This is the cheap road,
   and it is the reason this node exists as a separate target rather than as
   a corollary.

3. **Read the answer off known approximation properties of `Gbar`.** Not
   available. Whether the large free Burnside groups and their relatives are
   sofic or LEF is exactly the delicate question recorded in attempt 4 of
   `operator-norm-restricted-burnside`, and soficity would in any case be an
   obstruction to neither conclusion: normalized Hamming approximations do
   not become operator-norm approximations.
