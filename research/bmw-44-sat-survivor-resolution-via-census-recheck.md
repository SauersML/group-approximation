---
rg: 2
id: bmw-44-sat-survivor-resolution-via-census-recheck
kind: route
title: The three survivors are among the census candidates, all of which carry an independently re-checked solver-free certificate, so the second alternative holds for each
target: bmw-44-sat-survivor-parity-kernels-not-left-orderable
requires:
  - bmw-census-solver-free-parity-kernel-certificates
  - bmw-census-sat-free-klein-chain-certificates
  - bmw-census-klein-power-chain-certificates
  - bmw-klein-frame-chain-certificates
  - bmw-klein-free-quaternionic-parity-kernels
  - bmw-census-survivor-cone-tree-certificates
  - bmw-census-radius6-cone-lemma-certificates
artifacts:
  - experiments/bmw-census-solver-free-recheck-2026-09-18/README.md
  - experiments/bmw-census-solver-free-recheck-2026-09-18/recheck.log
---

The target says that for each of `40_40#193`, `#281` and `#332`, either `Γ` is reducible or `Γ^+`
is not left-orderable.

**Where the three classes sit.** They are candidates of pattern `40_40`: neither automaton image is
certified finite at cap 4000. `recheck.log` reproduces this, and so does `bigcap.log` at cap 60000.

**The certificate.** By `bmw-census-solver-free-parity-kernel-certificates`, every candidate of the
20 census patterns of degrees (3,3), (4,3), (4,4) and (5,3) has a certificate that `Γ^+` is not
left-orderable. Each certificate was re-checked from the census squares by a fresh script, with no
SAT solver.

For the three survivors, the re-check accepts two different four-term Klein chains each:
- `chains_census_40_40.json`, from `bmw-census-sat-free-klein-chain-certificates`;
- `chains_40_40.json`, from `bmw-40-40-193-281-332-klein-chain-proof`. These chains are:
  - `#281` and `#332`: `h0h2, v3v0v2v3, h3h1h2h3, v1v2`;
  - `#193`: `h0h1, v0v3, h3h0h2h3, v2v0v1v2`.

Each step `x_{i+1} x_i x_{i+1}^{-1} = x_i^{-1}` forces `|x_i| < |x_{i+1}|` (Lemma K of
`bmw-census-solver-free-parity-kernel-certificates-proof`). So no left order exists on `Γ^+`, and
the second alternative holds for all three. ∎

**Why the other certificate claims are required.** This route places the survivors inside the
complete solver-free resolution of the census, not only beside it. The certificate claims are:
- the Klein chains (w6c);
- the Klein-power chains (w7);
- the frame chains (w8);
- the quaternionic cone trees (w9);
- the radius-4/6 cone trees (w10);
- the radius-6 cone lemmas (w11).

Together they are the data that the re-check verifies, and it finds all of them valid and covering
every candidate. Hence the census theorem `bmw-degree-44-53-parity-kernels-not-left-orderable` holds
without its three exceptions: every irreducible BMW lattice of degree (3,3), (4,3), (4,4) or (5,3)
has a non-left-orderable parity kernel.

**Independence.** This route is independent of the DRUP certificate of
`bmw-40-40-193-281-332-parity-kernels-not-left-orderable` (w5-107b) and of any SAT solver.
