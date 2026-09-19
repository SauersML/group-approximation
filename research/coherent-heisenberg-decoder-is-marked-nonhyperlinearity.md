---
rg: 2
id: coherent-heisenberg-decoder-is-marked-nonhyperlinearity
kind: claim
title: The positive-density Leavitt decoder is equivalent to excluding a surviving HS mark
invalidates:
  - nonhyperlinear-from-coherent-heisenberg-module-decoder
distinct_from:
  coherent-heisenberg-multiplicity-decoder: that states the universal decoder; this identifies its exact logical strength rather than supplying the missing same-reservoir occurrence.
  approximate-relative-leavitt-cell-kills-active-trace: that proves the terminal trace floor once a corner is supplied; this combines that floor with the decoder's universal quantifier and simplicity.
---

**ESTABLISHED LOGICAL BOUNDARY.**  Let `G` be the simple binary-Leavitt
elementary group and let `z!=1` be a fixed elementary root.  Let `D_z` denote
the assertion that every normalized-Hilbert--Schmidt asymptotic
representation in which `z` stays a positive distance from the identity
supplies a common corner `P_n` of uniformly positive normalized trace and
four contractions `S_0,S_1,T_0,T_1` on that corner such that

```text
||T_i S_i-P_n||_(2,P_n) -> 0,                         (CHD1)
||S_0T_0+S_1T_1-P_n||_(2,P_n) -> 0.                   (CHD2)
```

Then `D_z` holds if and only if no normalized-Hilbert--Schmidt asymptotic
representation keeps `z` nontrivial.  Since `G` is simple, this is equivalent
to nonhyperlinearity of `G`.

Indeed, for every nonzero finite-dimensional corner `P`, normalized corner
trace and cyclicity give the dimension-free inequality

```text
1 <= ||T_0S_0-P||_(2,P)
   + ||T_1S_1-P||_(2,P)
   + ||S_0T_0+S_1T_1-P||_(2,P).                       (CHD3)
```

Thus the proposed output `(CHD1)--(CHD2)` cannot exist.  Decoder validity
therefore rules out every instance of its premise, while absence of such an
instance makes the universal decoder assertion vacuously true.  A surviving
mark gives a nontrivial homomorphism into a tracial matrix ultraproduct; its
kernel is normal, so simplicity makes that homomorphism injective.

Accordingly `coherent-heisenberg-multiplicity-decoder` cannot serve as a
lower-level decomposition of `non-hyperlinear-group`.  A nonvacuous
replacement must name an additional full-presentation occurrence and prove a
quantitative same-reservoir or boundary-payment estimate.  No Property `(T)`,
Kazhdan projection, stability theorem, or character-rigidity input occurs in
this logical audit.

DERIVATION
coherent-heisenberg-decoder-logical-boundary-proof
