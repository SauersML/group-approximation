---
rg: 2
id: atlas-reverse-dictionary-does-not-close-ee-return
kind: claim
title: The reverse dictionary does not close the common x12(ee) return mode
invalidates:
  - atlas-reverse-seam-authenticates-ee-common-mode
artifacts:
  - experiments/atlas_first_nonscalar_mixed_row_audit.py
distinct_from:
  atlas-reverse-dictionary: that proves the twelve atlas generators lie in the rank-five root image and hence gives global presentation surjectivity; this audits whether those twelve literal seam rows add the missing occurrence direction to the first common-RHS return star.
  atlas-first-common-rhs-return-star-has-rank-two: that computes the three-return star before any chart seam is adjoined; this appends the complete reverse dictionary and proves that its literal incidence still misses the common two-letter RHS.
  leavitt-range-sum-fold-does-not-pay-reynolds: that constructs an exact finite model retaining transverse Reynolds leakage across the scalar range-sum fold; this is the narrower exact coefficient census for the Atlas reverse seam and makes no claim about every mixed forward/reverse consequence.
---

**ESTABLISHED EXACT OCCURRENCE CENSUS.** Append the complete twelve-row
reverse dictionary to the first common-RHS return star

```text
P_3-R=0,       P_4-R=0,       P_5-R=0,
R=x_12(ee).                                             (RSE1)
```

Eight reverse rows identify an atlas generator with one rank-five root. The
only four nontrivial seams identify an atlas generator with the following
two-factor products:

```text
p1_01 = x_35(E)x_45(F),       p1_10 = x_53(e)x_54(f),
p2_01 = x_15(E)x_25(F),       p2_10 = x_51(e)x_52(f).   (RSE2)
```

Their translated-relator syllable lengths are `18,17,18,17`, and their
Atlas `X`-lengths are `71,67,71,67`. The MSI audit reconstructs the exact
twelve rows from the join-code refinement and checks these values.

Every factor in every reverse row has coefficient in the one-letter set

```text
{1,e,f,E,F}.                                            (RSE3)
```

In particular, no reverse row contains the common two-letter occurrence
`x_12(ee)`. The only reverse factor in the root subgroup `(1,2)` is the
single root `x_12(1)` occurring in the one-factor row for `p1_23`.

Consequently all twelve reverse rows project to zero on the four literal
return-star columns `(P_3,P_4,P_5,R)`. The star matrix remains

```text
[ I_3  -1_3 ],
rank[C D]-rank(D)=3-1=2.                               (RSE4)
```

Adding the atlas-generator and single-letter-root columns of the reverse
rows as mandatory nuisances adds the same row space to the total and
nuisance matrices. It cannot create the missing third quotient direction.
Equivalently, the common seam vector

```text
(P_3,P_4,P_5,R)=(T,T,T,T)                              (RSE5)
```

survives every row in this augmented literal family.

This refutes the proposal that the reverse dictionary **by itself** is an
independent authentication of `x_12(ee)`. It does not rule out a longer
normal-closure consequence mixing forward dictionary, St3, and chart rows.
The next viable family must contain a row whose occurrence data actually
meets the two-letter RHS (or prove a quantitative occurrence-transfer
theorem from the one-letter chart seam); presentation surjectivity alone is
not such a transfer.

DERIVATION
atlas-reverse-dictionary-ee-return-proof
