---
rg: 2
id: mf-camouflage-surgery-proof
kind: route
title: Kill one vertex in every MF target and apply the universal property of the amalgam
target: mf-camouflage-surgery
requires:
  - hilbert-hotel-self-saturated-non-mf
  - mf-radical-functoriality
---

Normal form for amalgamated free products embeds both vertices, so `d` is
nontrivial in `C_d(Q)`.  The maps which are trivial on `B` and equal to the
projection `Q x D -> Q` on the other vertex agree on `D`; they induce the
split epimorphism `pi_Q`.

Certainly `d` lies in its kernel.  Conversely, quotienting by the normal
closure of `d` kills `B`, because `d` normally generates `B`, and kills only
the `D` coordinate in the second vertex.  The resulting quotient is `Q`, so
`ker(pi_Q)=normalClosure(d)`.

Let `f:C_d(Q)->T`, where `Hom(B,T)={1}`.  Its restriction to `B` is trivial,
so it kills the common subgroup `D`.  On the second vertex,

```text
f(q,x)=f(q,1)f(1,x)=f(q,1),
```

so that vertex map factors uniquely through `Q x D -> Q`.  The amalgam
universal property gives a unique `f_bar:Q->T` with
`f=f_bar*pi_Q`.  Surjectivity of `pi_Q` gives uniqueness and naturality.
If `T` is MF, the hypothesis follows from `Rad_MF(B)=B` and radical
functoriality; it also holds directly for every norm-corona unitary target.

For the finitely presented specialization take the rank-twenty
Hilbert-hotel quotient and its full root defect.  The defect is nontrivial,
normally generates the quotient, and every MF-target map out of that quotient
is trivial.  Both vertex groups are finitely presented when `Q` is, and `D`
is cyclic; the standard finite amalgam presentation therefore makes
`C_d(Q)` finitely presented.
