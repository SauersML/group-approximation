---
rg: 2
id: kaplansky-universal-group-via-colimits-and-finite-fields
kind: route
title: Embed every finite presentation and transfer the finite inverse witness
target: kaplansky-direct-stable-finiteness-one-universal-group
requires:
  - whitehead-universal-finitely-presented-container
  - subgroup-supported-one-sided-inverse-rigidity
---

Choose the fixed two-generator finitely presented group `V` from
[[whitehead-universal-finitely-presented-container]]. It contains every
finitely presented group.

Fix a field `k` and suppose `k[V]` is directly finite. Direct finiteness
passes to subgroup group rings: if `H<=V` and `A,B in k[H]` satisfy
`AB=1`, the same equality in `k[V]` gives `BA=1`, and injectivity of
`k[H]->k[V]` returns the equality. This is also the scalar case of
[[subgroup-supported-one-sided-inverse-rigidity]].

Every group is a directed colimit

```text
G=colim_i P_i
```

of finitely presented groups, using finite generator-and-relator
approximants of any presentation. Every `P_i` embeds in `V), so every
`k[P_i]` is directly finite. Since `k[G]=colim_i k[P_i]`, any alleged
failure `AB=1`, `BA!=1` lifts to one stage and its equality holds at a
later stage; the inequality remains there because its colimit image is
nonzero. Hence every `k[G]` is directly finite.

Dykema--Juschenko's theorem, as recorded in
Ceccherini-Silberstein--Coornaert--Phung, *First-order model theory and
Kaplansky's stable finiteness conjecture for surjunctive groups*, Groups
Geom. Dyn. 19 (2025), 495--503, doi:10.4171/GGD/885, Remark 4.2, says

```text
k[G] is stably finite
  <=>
k[G x H] is directly finite for every finite group H.
```

Global direct finiteness therefore gives global stable finiteness. Global
stable finiteness applies to `V`, and stable finiteness implies direct
finiteness, proving the four-way equivalence.

For coefficients, Lemma 3.3 of the same paper proves that stable finiteness
over every finite field implies stable finiteness over every field for one
fixed group; Remark 4.3 gives the corresponding direct-finiteness transfer.
Apply either to `V`, then use the four-way fixed-field equivalence. The
reverse implications are immediate.

Finally, `V` has exactly all finite torsion orders by its construction. It
contains the existing finitely presented nonsofic and non-MF witnesses, so
subgroup heredity makes it nonsofic and non-MF. QED
