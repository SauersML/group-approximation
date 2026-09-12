---
rg: 2
id: rank-density-is-quadratic-trace-selection
kind: claim
title: Approximate ranks are equivalent to uniform quadratic trace selection, including an exact ASH stage criterion
distinct_from:
  rank-density-and-strict-comparison-give-purity: that derives purity from rank density with comparison; this replaces rank density itself by a quantitative degree-two moment condition without comparison.
  ah-algebras-realize-ranks-approximately: that proves rank density for AH algebras; this proves an equivalence for arbitrary unital algebras and identifies the unresolved finite-stage selection condition in ASH.
artifacts:
  - research/artifacts/ash-rank-quadratic-selection-2026-09-11.md
---

For a unital C*-algebra `A` with nonempty trace space and a continuous real
function `f` on `T(A)`, use unnormalized matrix traces and put

```text
Delta(f)=inf_{m,a in M_m(A)_+} sup_tau |d_tau(a)-f(tau)|,
E(f)=inf_{m,0<=b<=1 in M_m(A)}
       max{sup_tau |tau(b)-f(tau)|, sup_tau tau(b-b^2)}.
```

Then `Delta(f)<=3E(f)` and `E(f)<=2Delta(f)`.

For an injective unital subhomogeneous inductive system with simple unital
non-elementary limit, rank density is further equivalent to the following
condition: for every positive element `h` in a stage and every `epsilon>0`,
a later stage has a positive contraction `b` in some finite matrix algebra
whose first moment agrees with that of the image of `h` within `epsilon`,
and whose defect `tau(b-b^2)` is below `epsilon`, for **every normalized
irreducible-fibre trace of that later stage**. Matrix amplification uses
`tau tensor Tr_m`, not a trace normalized again by `m`.

The exact fibre formulas, compactness proof removing nonextendible stage
traces, and quantified negation are in Sections 2--3 of the artifact. In
particular, the global universal ASH selection assertion remains open.
