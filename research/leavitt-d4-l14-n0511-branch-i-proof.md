---
rg: 2
id: leavitt-d4-l14-n0511-branch-i-proof
kind: route
title: Separate the copy-zero conjugacy, split the alternating word, and reduce the scalar carrier
target: leavitt-d4-l14-n0511-branch-i-needs-nontrivial-carrier
requires:
  - leavitt-d4-l14-six-winner-profile-has-two-classes
---

Reading the four prefix faces of `---++-+-++++++` gives `(N51-2)` directly;
it agrees with `C0=g0_0`, `A1=g3_3` and the carrier equations recorded in
the classification claim.  Malnormality of free factors proves `(N51-3)`.

For the alternating word in `(N51-2)`, branch I of the noncrossing
partition is exactly `(N51-4)`.  Applying the four copy retractions to the
third carrier equation leaves only `(N51-5)` in copies zero and three; after
`(N51-4)`, direct cancellation of the intervening `H H^-1` pairs shows that
the full equation is the same identity.  Substitution in `H` gives `(N51-6)`.

If `(N51-6)` is one, the two free factors force `k=a=1`.  Equations
`r=1`, `adft=1`, `kb=ta`, and `q=bc=1` then give
`l=1`, `dft=1`, `b=t`, and `c=t^-1`.  Substitution in

```text
K=H^-1 B0 H^-1 B1 H^-1 E6
```

gives `(N51-7)`.  The case split on `i,j,t` in the claim is ordinary reduced
free-product normal form and proves the final fence.

