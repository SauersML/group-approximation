---
rg: 2
id: torsion-free-universal-quotient-via-chiodo
kind: route
title: Read Chiodo 1107.1489 sections 3.1-3.8 for the effective torsion-free radical
target: torsion-free-universal-quotient-recursively-presented
requires: []
artifacts:
  - research/artifacts/whitehead-vanishing-audit-2026-08-17.md
---

Literature import.  Direct reading of arXiv:1107.1489v4 (Maurice Chiodo,
*On torsion in finitely presented groups*), pages 4--5, on 2026-08-17.
Statements read and checked, not merely cited:

* **Definition 3.1** `Tor_0(G) = {e}`,
  `Tor_{i+1}(G) = << { g : g Tor_i(G) in Tor(G/Tor_i(G)) } >>^G`,
  `Tor_oo(G) = union_i Tor_i(G)`, a normal subgroup.
* **Lemma 3.2** `G/Tor_oo(G)` is torsion-free.  Proof checked: if
  `g^n` in `Tor_oo(G)` then `g^n` in `Tor_i(G)` for some finite `i`, so
  `g` in `Tor_{i+1}(G)`.
* **Proposition 3.3** `rho(G) = Tor_oo(G)`, the torsion-free radical.
* **Corollary 3.4** `G/Tor_oo(G) = G^tf`, the universal torsion-free
  quotient, with the factorization property through any homomorphism to a
  torsion-free group.  The universal property and uniqueness are set out on
  page 4 (`h` surjective makes the factoring map unique).
* **Lemmas 3.5--3.7** for a countably generated recursive presentation the
  word problem set is r.e., hence so is the set of words representing torsion
  elements, hence so is `T_oo`, uniformly over `i` and over presentations.
* **Proposition 3.8** the uniform algorithm: on input a countably generated
  recursive presentation `P = <X|R>`, output `P^tf = <X|R'>` with `R` inside
  `R'`, a countably generated recursive presentation of the torsion-free
  universal quotient, with the associated surjection extending `id_X`.

Chiodo notes that `Tor_1` alone does not suffice -- his page 4 gives
`<x,y,z | x^2, y^3, xy = z^6>` with `Tor_1 != Tor_oo` -- so the transfinite
flavour of the construction is necessary, and any attempt here to shortcut to
"quotient by the torsion elements" would be wrong.

Trust surface: this is a `requires: []` literature import.  What is imported
is a construction and an algorithm, both verified against the printed proofs
this session; nothing is taken on the paper's authority alone.
