---
rg: 2
id: britton-root-leak-bound-is-sharp-at-every-dyadic-depth
kind: claim
title: The two-root Britton leak bound is sharp at every dyadic depth
invalidates:
  - sl3-dyadic-exclusion-by-stronger-britton-root-leak
artifacts:
  - research/one-denominator-torus-dyadic-clock-proof.md
distinct_from:
  finite-dyadic-towers-are-neutral-with-one-torus-edge: that realizes all scalar overlaps of two mutually unbiased dyadic towers and obtains only the universal lower bound on root leakage; this simpler cyclic-clock packet computes the two individual root defects and attains equality in the Britton-leak estimate.
  unbalanced-torus-word-localizes-britton-leak: that proves the dimension-free lower bound; this is its sharpness example at every spectral depth.
  unbalanced-torus-blocks-spectator-free-lamp-models: that rules out a separated free-lamp factor over an exact ambient arithmetic representation; this local packet omits the remaining lattice relations and shows the root-leak inequality itself cannot be strengthened from the displayed data.
---

Use the displayed torus packet of
`unbalanced-torus-and-swap-commutation-do-not-control-fold-square`.  For
every `R>=1` there is an exact finite-dimensional assignment with an
order-`2^R` unitary `T`, a denominator transporter `H`, and a coherent
spectral tower

```text
q_(r,j)=1_(I_(r,j))(T),       1<=r<=R, 0<=j<2^r,          (ODC1)
q_(r,j)^h=H q_(r,j) H^*,                                     (ODC2)
```

such that:

```text
sum_j q_(r,j)=1,          tr(q_(r,j))=2^(-r),
q_(r,j)=q_(r+1,2j)+q_(r+1,2j+1),                            (ODC3)

[T,A_12]=[T,B_21]=[T,W_12]
 =[T,A_23]=[T,B_32]=[T,W_23]=0,                             (ODC4)

R_tor=1,                  tr(T^*H^*TH)=0.                   (ODC5)
```

Thus the base dyadic atoms commute with every displayed base coefficient,
the adjacent atoms are transported by the same physical `H`, the fixed
unbalanced arithmetic closure is exact, and the first conjugate-letter
cross-Gram has its canonical free value.

Unlike the Walsh packet in
`finite-dyadic-towers-are-neutral-with-one-torus-edge`, this construction
does not assert the full scalar overlap table of the two spectral towers.
Its new content is the exact calculation of both root defects below.

The construction also shows that the dimension-free Britton-leak estimate
is sharp.  With `T_1=H^*TH`, the two negative-root defects from `(UBL1)` are

```text
eta_21=sqrt(2),             eta_32=0.                       (ODC6)
```

All other errors in `(UBL3)` vanish, so `(UBL3)` is equality:

```text
eta_21+eta_32=sqrt(2).                                    (ODC7)
```

The first mixed packet therefore does produce a genuine, dimension-free
conclusion, but it is localization rather than contradiction: the free
coset tower has exactly enough transverse root motion to pay it.

This does not model the full `SL_3(Z)` presentation and does not refute
`sl3-outliers-have-no-dyadic-a2-pvm-tower`.  It proves the sharp scoped
firewall.  No stronger lower bound on `eta_21+eta_32`, and no assertion that
both root defects must be positive, follows from the variables in
`(UBL1)--(UBL3)`, even after arbitrary dyadic refinement.  A continuation
must use an omitted genuine lattice identity coupling the leaking negative
root to the rest of the common actor, or matrix-coordinate information
absent from that energy ledger.

DERIVATION
one-denominator-torus-dyadic-clock-proof
