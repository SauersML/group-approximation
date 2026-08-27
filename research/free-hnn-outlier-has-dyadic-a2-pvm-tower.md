---
rg: 2
id: free-hnn-outlier-has-dyadic-a2-pvm-tower
kind: claim
title: Every free SL3 HNN outlier carries a coherent dyadic A2 PVM tower
distinct_from:
  hnn-stable-letter-rounds-to-finite-order: that extracts one balanced finite-order unitary for every chosen order; this retains the common spectral source and records the nested projection tower, its entire coset orbit, and one literal Steinberg loop at every depth.
  full-hnn-regularity-is-a-quasiregular-unitary-orbit: that gives the orthonormal orbit of the Haar generators themselves; this resolves every generator into coherent dyadic spectral atoms and computes their translate overlaps.
  closed-a2-loop-still-leaves-swap-fold-free: that finite packet retains one balanced projection while satisfying two shortest return relations; this consequence of the full Haar law supplies all dyadic refinements simultaneously and the full coset-indexed free family.
  arithmetic-global-pvm-does-not-bypass-coset-action-gate: that proves a rounded global binary-lamp PVM still leaves an asymptotic coset-action model; this retains the diffuse free-lamp tower and literal rank-two coherence, but does not claim that PVM existence alone escapes that same gate.
---

Put `C=SL_3(Z)<A=SL_3(Z[1/2])`, `B=L(C)`, and suppose an enemy for
`sl3-ambient-outliers-carry-no-free-hnn-letter` exists: a trace-preserving
`pi:L(A)->M` into a tracial matrix ultraproduct and a Haar unitary
`k in pi(B)'` free from `pi(L(A))` with amalgamation over `pi(B)`.

For `r>=1` and `0<=j<2^r`, let `I_(r,j)` be the `j`-th dyadic arc of the
circle and define

```text
q_(r,j)=1_(I_(r,j))(k).                                  (DPT1)
```

Then the `q_(r,j)` form a coherent tower of exact PVMs in `pi(B)'`:

```text
sum_j q_(r,j)=1,       tau(q_(r,j))=2^(-r),
q_(r,j)=q_(r+1,2j)+q_(r+1,2j+1).                       (DPT2)
```

For a left coset `x=aC`, put

```text
q_(r,j)^x=pi(a)q_(r,j)pi(a)^*.                          (DPT3)
```

This is well defined.  The actor acts covariantly on the tower, and the
diffuse abelian algebras

```text
D_x=W^*(q_(r,j)^x:r>=1,0<=j<2^r)
```

are freely independent in the canonical lamp trace.  In particular, for
distinct cosets `x!=y`,

```text
tau(q_(r,i)^x q_(s,j)^y)=2^(-r-s),                      (DPT4)
```

whereas atoms in the same level and same coset are orthogonal unless their
labels agree.

The tower carries literal rank-two lattice holonomy.  Put

```text
u=x_23(1),       v=x_31(-1),       w=x_21(-1).
```

The actual Steinberg relation `[u,v]=w` gives, at every depth, label, and
coset,

```text
q_(r,j)^([u,v]x)=q_(r,j)^(w x).                         (DPT5)
```

Thus one enemy supplies not one rounded swap projection but arbitrarily
fine, nested, trace-flat PVMs on the whole coset apartment, with every
Steinberg loop closing on the same physical atoms.  By
`sl3-amalgamated-free-enemies-are-ambient-extension-outliers`, the actor
carrying this tower is uniformly separated from every exact
same-dimensional ambient representation.

This is a reduction, not an exclusion theorem.  Every fixed depth and fixed
finite coset window is compatible with the existing finite-lamp and
two-letter Morita countermodels.  The remaining matrix-specific datum is
simultaneous coherence over unbounded dyadic depth together with the one
common approximate arithmetic actor.  The corresponding explicit residual
is `sl3-outliers-have-no-dyadic-a2-pvm-tower`.  In particular,
`arithmetic-global-pvm-does-not-bypass-coset-action-gate` already rules out
treating the tower merely as a global PVM: without a same-carrier
matrix-coordinate estimate, it returns to the original coset-action
approximation problem.

DERIVATION
free-hnn-dyadic-a2-pvm-tower-proof
