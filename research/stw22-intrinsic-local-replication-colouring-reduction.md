---
rg: 2
id: stw22-intrinsic-local-replication-colouring-reduction
kind: claim
title: Intrinsic local replication suffices over every finite-dimensional base
distinct_from:
  stw22-finite-dimensional-colouring-from-local-lifts: that theorem is formulated in a trivial UHF field and uses fixed orthogonal corners in one ambient factor; this reduction needs neither a common ambient factor nor locally trivial fibres and asks only for an exact local tuple inside the abstract bundle.
  stw22-locally-trivial-finite-dimensional-bundles: that theorem obtains the local tuples from product charts; this isolates the strictly weaker local input consumed by the colouring argument.
  stw22-zero-dimensional-factor-bundles-have-uniform-traces: that theorem promotes intrinsic lower semicontinuity to global tuples using disjoint clopen refinement; this identifies the local-selection input needed when the base has positive dimension.
artifacts:
  - research/artifacts/stw22-positive-dimensional-intrinsic-selection-frontier-audit-2026-08-30.md
---

Let `K` be compact and metrizable with `dim(K)=d<infinity`, and let `M`
be a factorial tracially complete C-star algebra over `K`, with uniform
trace expectation `E:M->C(K)` and factor traces `tau_x=ev_x o E`.

Assume the following intrinsic local replication property.  If `m>=1`,
`V subset K` is open, and `a in M_+` is a contraction which vanishes
outside a subset which is closed in `K` and contained in `V`, and satisfies

```text
sup_(x in V) tau_x(supp(a_x)) < 1/m,                    (ILR1)
```

then every point of `V` has a neighbourhood `O subset V` and contractions
`w_1,...,w_m in M` such that, in every fibre over `O`,

```text
(w_j)_x^*(w_j)_x=a_x,
((w_i)_x(w_i)_x^*)((w_j)_x(w_j)_x^*)=0       (i!=j).   (ILR2)
```

Then every norm/uniform-`2`-norm fibre gap `K_x/J_x` has no nonzero bounded
positive trace.  Consequently every tracial state on `M` is integration of
the designated fibre traces against a probability measure on `K`, and is
continuous for the uniform `2`-norm.

More quantitatively, every positive contraction `a` which is zero off a
specified subset closed in `K` and contained in `V`, and satisfies `(ILR1)`,
admits contractions

```text
v_(j,r) in M,       1<=j<=m, 0<=r<=d,
```

such that

```text
sum_(r=0)^d v_(j,r)^*v_(j,r)=a                    (1<=j<=m),
norm(sum_(j=1)^m sum_(r=0)^d v_(j,r)v_(j,r)^*)<=d+1.   (ILR3)
```

For `d=1`, this gives a two-colour replication bound, independent of `m`.
The unresolved step for an arbitrary one-dimensional factorial
bundle is only the passage from fibrewise, lower-semicontinuous solvability
of `(ILR2)` to an exact continuous local tuple.  No fixed comparison corner,
common factor, or bundle chart is needed after that local tuple exists.
