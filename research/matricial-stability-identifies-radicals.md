---
rg: 2
id: matricial-stability-identifies-radicals
kind: claim
title: Matricial stability identifies the MF radical with the finite-dimensional residual
distinct_from:
  map-matricial-stability-non-mf: That claim is the special case in which minimal almost periodicity makes the finite-dimensional residual the whole group; this one computes Rad_MF for every matricially stable group, so a nontrivial finite-dimensional residual alone already obstructs MF, with no almost-periodicity hypothesis.
  corona-hs-radical-is-finite-residual: That claim computes the 2-norm-invisible set of one concrete group with no stability hypothesis; this one computes the operator-norm MF radical of every matricially stable group.
---

For a countable group `G` write

```text
Rad_fd(G)  =  intersection of ker(pi) over all finite-dimensional
              unitary representations pi of G.
```

Always `Rad_MF(G) <= Rad_fd(G)`.  If `G` is **matricially stable** in
Dadarlat's point-norm sense (`dadarlat-matricial-stability-obstruction`:
every asymptotic homomorphism `phi_n : G -> U(k_n)`, not necessarily
separating, is pointwise operator-norm close to a sequence of genuine
homomorphisms), then

```text
Rad_MF(G)  =  Rad_fd(G):
```

exact finite-dimensional blindness automatically becomes MF blindness, and
the MF reflection of `G` coincides with its maximal residually
finite-dimensional quotient.  Consequences:

- a matricially stable group with `Rad_fd(G) != 1` is **not MF** — no
  torsion, no mark, no central element, no compression data anywhere in the
  hypotheses;
- for matricially stable groups the MF radical is computable by
  finite-dimensional representation theory alone.

`mf-camouflage-surgery-preserves-matricial-stability` now supplies concrete
finitely presented stable groups with nontrivial finite-dimensional
residual.  Starting from a stable MF group such as a finite-rank free group
or `Z`, the camouflage group remains stable while its finite-dimensional
residual becomes the nontrivial singly normally generated hidden kernel.
