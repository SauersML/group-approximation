---
rg: 2
id: reduced-mf-hyperlinear-radical-in-amenable-radical
kind: claim
title: Reduced MF makes every element outside the amenable radical tracially visible
distinct_from:
  mf-implies-hyperlinear: that asks whether bare operator MF gives tracial visibility of every element; this proves visibility off the amenable radical from the stronger hypothesis that the reduced group C-star algebra is MF.
  kt-q2-double-reduced-algebra-has-unique-trace: that removes trace selection for one group with trivial amenable radical; this needs no uniqueness of traces and bounds the invisible set by the amenable radical for every group.
  mf-finite-normal-tracially-visible: that makes finite normal subgroups visible under bare operator MF; this makes the complement of the amenable radical visible under reduced MF.
---

ESTABLISHED.  Let `G` be a countable group and suppose `C*_r(G)` admits an
injective *-homomorphism into a norm matrix corona
`prod_n M_(d_n) / sum_n M_(d_n)`.  Then every `s notin R_a(G)` is tracially
visible in the sense of `hyperlinear-elementwise-visibility`, with constant
`c_s = 1/2`.  Equivalently,

```text
Rad_hyp(G) <= R_a(G),
```

where `Rad_hyp(G)` is the intersection of the kernels of all homomorphisms from
`G` into unitary groups of tracial matrix ultraproducts, i.e. the set of
elements which are not tracially visible.

The visibility is witnessed by **operator-norm** models: unitary lifts
`u_n(s)` of the corona embedding have operator-norm multiplicative defects
tending to zero and

```text
tr_(d_n)(u_n(s)) -> 0        for every s notin R_a(G).
```

So under reduced MF the only possible obstruction to hyperlinearity sits inside
the amenable radical.  When the radical is trivial this is the unique-trace
route used for the Kun--Thom double; the present statement needs no uniqueness
and applies to groups with nontrivial amenable radical as well.

A short combination of `bkko-reduced-traces-concentrate-on-amenable-radical`
with the tracial quotient of the corona; no priority claim is made.
