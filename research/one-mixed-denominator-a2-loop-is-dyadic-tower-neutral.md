---
rg: 2
id: one-mixed-denominator-a2-loop-is-dyadic-tower-neutral
kind: claim
title: One two-sided mixed denominator A2 loop is neutral on every finite dyadic tower
invalidates:
  - sl3-dyadic-tower-exclusion-from-one-mixed-denominator-loop
artifacts:
  - research/mixed-denominator-dyadic-tower-countermodel-proof.md
distinct_from:
  p3-denominator-steinberg-word-is-multiplicity-blind: that cancels a multiplicity gauge in a single transported Chevalley triangle; this combines a two-sided denominator loop with the unbalanced torus closure, both competing A2 returns, and exact free-lamp PVM overlaps at every prescribed dyadic depth.
  finite-dyadic-towers-are-neutral-with-one-torus-edge: that realizes the full scalar overlap table and torus word but deliberately omits a common rank-two actor; this uses one finite common actor satisfying the closed A2 packet and the mixed denominator identity on the same physical lamp atoms.
  finite-sl3-loop-packets-are-dyadic-tower-neutral: that retains every lattice relation but does not cross a denominator edge; this crosses both orientations of the edge and retains the first mixed denominator-root commutator.
---

Let `p=2`, `h=diag(2,1,1/2)`, and use the displayed root names from
`closed-a2-loop-still-leaves-swap-fold-free`.  The first genuinely
two-sided mixed relation is

```text
[h x_21(-1) h^(-1),x_13(1)]=h^(-1)x_23(-1)h.          (MDT1)
```

For every `R>=1` there is a finite-dimensional exact packet containing:

1. an actor satisfying the unbalanced torus word, both closed `A_2`
   returns, the two rank-one doubling/Weyl factorization packages, and
   `(MDT1)`;
2. an order-`2^R` lamp `T` commuting with every displayed lattice
   coefficient;
3. its nested trace-flat spectral PVMs `q_(r,j)`, `r<=R`; and
4. the actor translates of those PVMs, with exact covariance on the same
   physical atoms and, for distinct actor/lattice cosets,

   ```text
   tr(q_(r,i)^x q_(s,j)^y)=2^(-r-s).                   (MDT2)
   ```

In particular the two paths in `(MDT1)` carry every `q_(r,j)^x` to the
same projection, not merely to projections with the same scalar moments.
Nevertheless the denominator coset is distinct from the base lattice
coset, and the first lamp/denominator commutator has regular trace zero.

Thus one denominator-crossing noncommuting loop does not exclude the
coherent dyadic tower, even after the first unbalanced closure and the
closed two-return packet are imposed.  The model intentionally omits the
genuine rank-one Weyl conjugacy which detects the residual sheet sign in
`closed-a2-loop-still-leaves-swap-fold-free`; it is not a representation of
the full arithmetic group.  The remaining route must couple that
rank-one authentication (or an equivalent common-actor coordinate) to the
all-depth denominator transport.

DERIVATION
mixed-denominator-dyadic-tower-countermodel-proof
