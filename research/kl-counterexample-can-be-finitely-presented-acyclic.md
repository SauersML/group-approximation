---
rg: 2
id: kl-counterexample-can-be-finitely-presented-acyclic
kind: claim
title: Any Kervaire--Laudenbach counterexample can be taken finitely presented, integrally acyclic and without proper finite-index subgroups
distinct_from:
  kl-counterexample-can-be-finitely-presented: that gives a finitely presented coefficient group with uncontrolled homology and possibly finite quotients; this passes it into the labelled Thompson envelope, which is acyclic and has no proper finite-index subgroups.
  kl-counterexample-can-be-finitely-presented-simple: that asks for finite presentation with simplicity and needs Boone--Higman; this gives finite presentation with acyclicity and no finite quotients, but not simplicity.
  kl-counterexample-can-be-two-generator-simple-acyclic: that is simple and acyclic but not known to be finitely presented; this is finitely presented and acyclic but not simple.
artifacts:
  - research/artifacts/hl-kl-minimal-counterexample-2026-09-14.md
---

If `kervaire-laudenbach-nonsingular-conjecture` fails at degree `m`, then it
fails at degree `m` over a finitely presented group `Q` such that:
- `H_n(Q; Z) = 0` for every `n >= 1`;
- `Q` has no proper finite-index subgroups;
- `Q` is strongly torsion generated.

If the finitely presented counterexample inside `Q` has solvable word problem,
so does `Q`.

`Q = V(P)` is the labelled Thompson group of a finitely presented
counterexample `P`.

## What it does not give

- **Simplicity:** `Z(V(P)) ≅ Z(P)`, and `V(P)` need not be simple.
- **Decidability:** it is transported, never created. The OPEN
  `kl-counterexample-can-have-solvable-word-problem` is untouched.

DERIVATION
kl-fp-acyclic-envelope-proof
