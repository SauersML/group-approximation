---
rg: 2
id: common-padding-erases-julia-derivation-density
kind: claim
title: Common exact padding erases every Julia derivation-rank density
distinct_from:
  weak-mf-embedding-not-reusable: that gives the general metric obstruction to reusing a weak-MF embedding; this preserves the globally conjugate Shulman normal form and computes the intrinsic derivation-rank density exactly.
  julia-derivation-rank-controls-fold: that identifies normalized generator-commutator rank as a necessary trace-spreading profile; this proves Shulman's operator-norm data cannot impose a lower bound on that profile.
  shulman-symmetric-double-has-no-stable-trace-upgrade: that corrects the scope of the published theorem; this gives an explicit coordinate operation preserving all of its norm conclusions while destroying the proposed rank density.
---

**ESTABLISHED SHULMAN PADDING NO-GO.** Let a globally conjugate
presentation-double coordinate be

```text
sigma:F->U(d),
rho(i_0(f))=sigma(f),          rho(i_1(f))=V^*sigma(f)V.   (CPJ1)
```

For every `N>=1`, add a common trivial summand:

```text
sigma^(N)(f)=sigma(f) directSum 1_N,
V^(N)=V directSum 1_N.                                  (CPJ2)
```

Then:

1. every kernel-edge commutator has exactly its old operator norm;
2. every fold-kernel word has value `rho(w) directSum 1_N`, hence exactly
   its old operator-norm gap;
3. every other word retains at least its old operator-norm separation;
4. multiplication defects are unchanged (and the vertex maps remain exact);
5. for every finite generating set `X` of `F`,

```text
R_X(sigma^(N),V^(N))=R_X(sigma,V),
R_X(sigma^(N),V^(N))/(d+N)->0.                          (CPJ3)
```

The same operation can be performed coordinatewise on a faithful
norm-corona model, with `N_n/d_n->infinity`. It preserves injectivity and
all operator-norm convergence used in Shulman's symmetric-double proof, but
makes the intrinsic Julia derivation-rank density tend to zero.

Therefore the published construction offers **no representation-independent
lower bound** on `R_X/d`, even after one has chosen a faithful corona
representation and the exact Julia normal form. Such a bound can only be a
selection property of a specially chosen, unpadded sequence.

The genuinely stronger selectable condition is trace data, not another norm
estimate: one must select coordinates and a fixed nontrivial fold word `w`
with

```text
liminf ||rho_n(w)-1||_(2,d_n)>0,                        (CPJ4)
```

or an equivalent nonzero matrix trace on the fold-support ideal. By
`julia-derivation-rank-controls-fold`, `(CPJ4)` forces a positive
derivation-rank density. Shulman's norm theorem does not select `(CPJ4)`;
adding it is precisely a trace-visible strengthening, not a consequence of
the Julia/quasicentral construction.

DERIVATION
common-padding-julia-rank-proof
