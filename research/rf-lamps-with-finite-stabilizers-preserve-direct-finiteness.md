---
rg: 2
id: rf-lamps-with-finite-stabilizers-preserve-direct-finiteness
kind: claim
title: Residually finite lamps over an action with finite stabilizers preserve direct finiteness at every matrix size
distinct_from:
  rf-lamp-permutational-wreaths-satisfy-stable-finiteness: that permits arbitrary stabilizers but assumes the base is residually finite; this permits any base satisfying the relevant group-algebra finiteness and requires finite stabilizers.
  residually-p-kernels-preserve-modular-stable-finiteness: that permits general extensions with a residually finite p-kernel in characteristic p; this permits arbitrary residually finite lamps and every characteristic for the specified permutation actions.
  one-invertible-certificate-fiber-forces-global-invertibility: that uses finite modifications in a scalar certificate full shift; this induces finite-dimensional lamp representations and applies the same finite-rank argument directly to a group algebra.
---

Let A be residually finite, let G act on a set X with finite point
stabilizers, let k be any field, and put

    W=A wr_X G=(direct_sum_X A) semidirect G.

The action permutes lamp factors without internal automorphism twists.
For each fixed n>=1,

    M_n(k[W]) is directly finite iff M_n(k[G]) is directly finite.

Thus this wreath construction preserves and reflects both direct
finiteness and stable finiteness. In particular, regular wreath products
A wr G have this property for every residually finite lamp group A and
every base G. Neither G nor W is assumed residually finite or sofic.
There is no restriction relating lamp orders to char(k), and no
finite-generation assumption.

The proof induces representations of finitely many lamp sites to G.
In each induced representation, every group-algebra element differs by
finite rank from its lamp-augmentation image acting through k[G]. These
representations jointly separate k[W]. A one-sided inverse consequently
becomes two-sided in every such representation whenever it does so in
k[G], forcing the identity in k[W].

Finite stabilizers are used to make the exceptional output rows finite.
`rf-lamps-preserve-stable-finiteness-for-arbitrary-actions` now removes
that condition for stable finiteness, using diagonal tensor algebras and
stabilizer corners. The fixed-matrix-size equivalence proved here is
stronger in that respect and is not asserted for arbitrary stabilizers.
No counterexample to either headline conjecture is constructed.
