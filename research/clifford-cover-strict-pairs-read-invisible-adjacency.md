---
rg: 2
id: clifford-cover-strict-pairs-read-invisible-adjacency
kind: claim
title: A strict pair on a Clifford cover must read an adjacency that no finite quotient of the site set separates
distinct_from:
  strict-pairs-transfer-to-table-realizations: that is the general table-transfer theorem; this applies it to Clifford covers by re-choosing the graph on the finitely many site pairs a strict pair reads.
  strict-automata-memory-keeps-finite-normal-kernel-residual: that constrains the memory group of a strict automaton over a finite normal extension; this constrains which adjacencies of the site graph the pair's products read.
  kun-thom-clifford-cover-nonsurjunctive: that is the open counterexample root on the cover; this is a necessary condition any witness for it must meet.
artifacts:
  - research/artifacts/clifford-cover-orbital-localization-2026-09-12.md
---

**Setting.**
- `G` is surjunctive, `X` is a `G`-set with finitely many orbits, and `S` is a `G`-invariant graph.
- `(tau, sigma)` is a strict pair over `E_S`, with memories `M` and `S_sigma` and a Garden of Eden on `Omega`.
- `R` is the finite set of site pairs read by the products `S_sigma M` and `Omega M` (artifact Section 0).

**Theorem (orbital form).** Some edge `{x,y}` of `S` in `R` is not *K-clean* for any finite-index normal
`K`. Here *K-clean* means two things:
- `K x != K y`;
- no non-edge `{x',y'}` in `R` has `{K x', K y'}` in the `G`-orbit of `{K x, K y}`.

**Coset form.** Take `X = G/Gamma` and write `Gammabar` for the profinite closure of `Gamma`. Then some
edge of `R` with orbital `g` has one of the following:
- `g in Gammabar`;
- some non-edge orbital `g'` of `R` in the profinite closure of `Gamma g Gamma` or `Gamma g^(-1) Gamma`.

**Complete graph** (holonomy form, artifact Theorem B'). Take the partial action graph on the read sites,
with the moves `x -> g_a x` used by the products. Some component, with base site `x_0` and holonomy group
`Hol <= Stab(x_0)`, contains two distinct sites `w x_0` and `w' x_0` with `w^(-1) w'` in the profinite
closure of `Hol`.

For the Kun--Thom pair (by `infranormal-subgroups-have-normal-profinite-closure`), the tables must do two
things:
- force a holonomy subgroup at some site whose profinite closure leaves that site's stabilizer;
- read two lamps in one fibre of `G/Gamma -> G/Gammabar`.

The radical-phase configuration is one such table.

**ESTABLISHED** by `clifford-cover-invisible-adjacency-proof` (artifact Section 3). No linearity is used,
so the filter holds for every alphabet.
