---
rg: 2
id: infranormal-nonnormal-has-infinite-compression-orbit
kind: claim
title: An infranormal non-normal subgroup has an infinite compression orbit, hence infinite index
distinct_from:
  finite-infranormal-subgroup-is-normal: that uses finiteness of the subgroup itself, so that conjugation preserves cardinality; this uses finiteness of the index and then goes further, producing a single element whose orbit on the coset space is infinite.
  infranormal-compact-closure-normal: that is about closures of the image in a compact group, where recurrence upgrades inclusions to equalities; this stays in the discrete group and is about the coset space.
artifacts:
  - research/artifacts/sofic-dividends-audit-2026-08-17.md
---

Let `Gamma <= G` be infranormal in the Kun--Thom sense — the compression
semigroup `P_Gamma = {g in G : g Gamma g^(-1) <= Gamma}` generates `G` — and
suppose `Gamma` is **not** normal in `G`.  Then there is `g in P_Gamma` with

    g^k not in Gamma   for every k >= 1,

so `g` has infinite order, the `<g>`-orbit of the base point of `X = G/Gamma`
is infinite, and `[G : Gamma]` is infinite.

The proof is three lines and is carried in Section B of the artifact: some
compressor must be strict, or the compression semigroup would sit inside the
normalizer and generate it; a strict compressor cannot have a power in
`Gamma`, because the descending chain
`Gamma >= g Gamma g^(-1) >= g^2 Gamma g^(-2) >= ...` would then close up and
force every inclusion to be an equality.

## Why it is worth a node

Both Kun--Thom hypotheses in this graph — Theorem A's for nonsoficity and
Theorem E's explicit elementary-group pair
(`kun-thom-nonsofic-wreath`) — are stated as *infranormal but not normal*.
Everything that is usually assumed alongside them about the size of the lamp
site space is a consequence, not an extra hypothesis:

* infinite index is what `no-invariant-mean-on-coset-space` needs, giving
  `kun-thom-stabilizer-not-co-amenable`;
* the infinite `<g>`-orbit is what
  `modular-radical-does-not-lift-direct-finiteness` needs, and it also
  produces a copy of the lamplighter `Z/2Z wr Z` inside every Kun--Thom
  wreath product;
* an external audit ingested on 2026-08-17 assumed the infinite index outright
  when applying property (T) to the stabilizer.  It is free.

It is the infinite-index companion of `finite-infranormal-subgroup-is-normal`:
that node says a finite infranormal subgroup is normal, this one says a
finite-index infranormal subgroup is normal and then extracts the orbit.
