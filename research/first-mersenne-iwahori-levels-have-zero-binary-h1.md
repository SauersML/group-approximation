---
rg: 2
id: first-mersenne-iwahori-levels-have-zero-binary-h1
kind: claim
title: The first two composite Mersenne Iwahori complexes have zero binary first cohomology
artifacts:
  - experiments/iwahori_binary_h1_probe.py
distinct_from:
  proper-torus-diagonal-code-is-incomplete-cover-curl: that defines the binary cellular complex at every level; this computes its exact cohomology at the first two composite levels.
  linear-cocycle-dimension-forces-phase-countersequence: that assumes an asymptotic linear cocycle-dimension bound; this verifies the strongest possible bound at two finite levels but does not extrapolate it.
  iwahori-uniform-infinitesimal-rigidity: that controls the characteristic-zero tangent complex; this audits the separate mod-two Smith-factor obstruction.
---

**ESTABLISHED FINITE COMPUTATION; ASYMPTOTIC EXTRAPOLATION IS OPEN.**
For the corrected global-sign quotients

```text
G_m=SL_2(Z/mZ)/{+-I}
```

and the proper-label complexes `K_(H,m)`, exact Gaussian elimination over
`F_2` gives

```text
m   |G_m|   |H|  |N|  |P|   V     E      F       rank(delta_1)  dim Z^1  dim H^1
15   1440     4    8   60   24    180    960          157          23       0
63 108864     6   12  378  288   9072  72576         8785         287       0
                                                               (MBH1)
```

Here `F` counts both order-three face orbits, including distinct face rows
paired by the nonglobal central sign. At both levels,

```text
rank_(F_2)(delta_1)=E-V+1,                              (MBH2)
Z^1(K_(H,m);F_2)=B^1(K_(H,m);F_2).                     (MBH3)
```

The computation is exhaustive, uses the presentation matrices
`x=w`, `t=u(1)`, `r=h(2)`, `a=xt`, `b=xt^2r`, and is reproducible with

```text
python experiments/iwahori_binary_h1_probe.py 15
python experiments/iwahori_binary_h1_probe.py 63
```

The asymptotic issue is an integral one. Let `D_Z` be any oriented
integer cellular curl matrix for `K_(H,m)`. Its reduction modulo two is
the unsigned binary parity matrix. If the characteristic-zero kernel is
exactly the vertex-coboundary space, then

```text
dim_(F_2) H^1
 =rank_Q(D_Z)-rank_(F_2)(D_Z),                          (MBH4)
```

which is the number of nonzero Smith invariant factors of `D_Z` divisible
by two. Thus a real singular gap or a real contracting homotopy does not
by itself prove the needed binary bound: one needs an odd full-rank minor,
an integral contraction with controlled powers of two, or a direct bound
on the number of even Smith factors.

Equations (MBH2)-(MBH3) show that no even Smith drop occurs at `m=15,63`.
They do not prove the hypothesis of the conditional phase-countersequence
theorem on infinitely many levels. The decisive open algebraic statement
is still

```text
dim_(F_2) H^1(K_(H,4^n-1);F_2)=O(V_n),                 (MBH5)
```

with vanishing as the strongest possibility. The diagonal decoder and
the non-hyperlinearity root remain open.

DERIVATION
mersenne-binary-h1-finite-audit-proof
