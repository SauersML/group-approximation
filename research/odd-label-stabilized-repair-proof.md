---
rg: 2
id: odd-label-stabilized-repair-proof
kind: route
title: Charge deep fibers by padding and transport bottom surplus through trivial blocks
target: odd-label-stabilization-does-not-enlarge-the-dyadic-repair-constant
requires:
  - mixed-crt-iwahori-repair-is-labeled-pure-dyadic-rounding
  - pure-dyadic-clifford-slots-have-a-uniform-one-third-gap
  - bounded-dyadic-conductor-iwahori-pairs-have-uniform-repair
---

Fix one odd label and omit `omega` from the notation. Let the two dyadic
dimensions be `d_+>=d_-`, put `delta=d_+-d_-`, and let `C` be the physical
dimension of their maximal common edge subrepresentation. The unweighted
fiber mismatch is

```text
l=d_++d_--2C,          so delta<=l.                    (OLP1)
```

Pad the smaller vertex packet by `delta` trivial representations. The
original common subrepresentation remains common after padding, so `(DCS4)`
applied at dimension `d_+` gives

```text
C <= d_+-(1/3)max(h_+,h_-).                            (OLP2)
```

Using `d_+-C=(l+delta)/2<=l` yields

```text
max(h_+,h_-)<=3l.                                      (OLP3)
```

After multiplying by `w_omega` and summing, both deep ranks together are at
most `6L`. Replacing a reducing summand of rank `r` by a trivial
representation changes generators on rank at most `r`; hence all deep
replacement costs are bounded by this physical-rank total. The restriction
mismatch after replacement is still `O(L)` by the triangle inequality.

For the bottom packets, restriction preserves dimension, so the weighted
`L^1` difference of their edge multiplicities dominates the absolute
weighted vertex-dimension difference in every label. This proves `(OLS2)`.
The conductor-at-most-one quotient is fixed; its irreducible dimensions are
at most two. If the exact surplus cannot be selected as a union of existing
blocks, changing one two-dimensional block to two trivial blocks exposes
one-dimensional units. Because a nonzero label imbalance is at least one
dyadic unit, the splitting cost is at most twice the paid imbalance.

Let `Delta_omega=w_omega(d_(+,omega)-d_(-,omega))`. The sum of the positive
`Delta_omega` equals the absolute sum of the negative ones. After splitting,
remove precisely the surplus trivial-dyadic blocks from their old odd labels
and relabel each of the two resulting equal-dimensional Hilbert pools by
copies of the globally trivial odd label tensored with the trivial dyadic
representation. Every nontrivial label is thereby cut down on its surplus
side to its smaller dimension; the trivial label grows equally on both
sides. This also covers labels having columns on only one vertex side. The
relabeling is an exact representation change and costs only the transported
physical rank.

Now every label has equal dimensions on the two sides. Apply the finite
bottom-diagram Hoffman correction label by label. If its unweighted bound is
`H_1 l_omega`, tensoring with `omega` changes `w_omega H_1 l_omega`
physical rank. Summing gives `H_1 L_bottom`, with no dependence on the label
set or weights. Combining the three steps proves a universal `H_mix`.

Finally a rank-`r` replacement of unitaries has squared normalized HS cost
at most `4r/d`. Together with `(MCR4)`, this is linear in the original edge
defect; the polar-alignment estimate already recorded in `(MCR6)` completes
the exact compatible repair.
