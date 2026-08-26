---
rg: 2
id: positive-benign-compiler-specializes-to-kernel-witness
kind: claim
title: A uniform benign compiler specializes to the graph kernel witness on the positive bridge
distinct_from:
  positive-scaffold-has-quotient-compatible-rf-witness: that refuted claim asked for a single map from the benign overgroup onto the non-finitely-presented quotient; this asks for specialization to a quotient-by-quotient finite-CEP graph witness and has no retraction.
  benign-witness-finite-quotients-refine-the-fold: that asks directly for the resulting profinite properties of a witness; this isolates the uniform relative-Higman construction which would supply those properties from the explicit cyclic fiber product.
---

Apply the three-generator bidirectional bridge to the exact FIN/INF switch,
obtaining a uniform finite-rank recursive presentation `Q_e=F/N_e` with

```text
e in INF: Q_e=B3(1),          e in FIN: Q_e contains E.        (PBK1)
```

Construct uniformly a finitely presented benign witness `(K_e,e_e,L_e)` for
`N_e<=F` such that, on the `INF` branch, its marked subgroup data are Tietze
equivalent to the graph kernel witness

```text
K_+=F times (F_2 times F_2),
L_+=graph(F -> B3(1) -> F_2 times F_2).                        (PBK2)
```

No effective test of the branch is allowed.  On the `FIN` branch only the
ordinary benign intersection property is required, so the subsequent rope
still embeds `Q_e` and therefore `E`.

## Attempts

The natural attack is a relative Higman construction over the fixed
epimorphism `Q_e->B3(1)`: all presentations in the family map onto the
positive bridge, and on `INF` that map is an isomorphism.  The construction
must arrange that the extra relative machine kernel disappears from the
marked benign data when this epimorphism is injective.  Ordinary Higman
embedding does not provide that specialization, and taking its product with
the graph witness leaves an uncontrolled finitely presented factor in
`K_e`, which can destroy MF and residual finiteness on the positive branch.
