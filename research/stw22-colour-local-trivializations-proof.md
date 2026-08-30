---
rg: 2
id: stw22-colour-local-trivializations-proof
kind: route
title: Colour chartwise weighted purifications without trivializing the bundle cocycle
target: stw22-locally-trivial-finite-dimensional-bundles
requires:
  - stw22-weighted-purification-all-sphere-fillings
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-locally-trivial-bundle-audit-2026-08-30.md
---

Fix `x in X`, a positive contraction `a in K_x`, a spectral threshold
`eta>0`, and an integer `m>=1`.  Put

```text
c=(a-eta)_+.
```

Because `||a(t)||_2 -> 0` at `x`, Chebyshev's inequality gives a
neighbourhood `V` of `x` on which

```text
tau_t(supp(c(t)))<1/(2m).                              (LT1)
```

Choose a central cutoff `h` which equals one near `x` and has support in
`V`, and replace `c` by `hc`.  This does not change its class modulo
`J_x`.  The support of the resulting section is contained in a compact
subset of `V`.

## Select inside each chart

Cover that compact support by finitely many bundle-trivializing open sets.
Take a finite refinement subordinate to these charts which is the union
of `d+1` discrete families, and choose a partition of unity `(f_alpha)`
whose supports are subordinate to the refinement.  Supports with the same
colour are pairwise disjoint.

Fix `alpha`, write `Z_alpha=supp(f_alpha)`, and use its containing product
chart to identify the restricted bundle with `Z_alpha times R`.  In that
copy of `R`, choose orthogonal projections

```text
e_(1,alpha),...,e_(m,alpha),
tau(e_(j,alpha))=1/m.                                 (LT2)
```

The positive field `c|_(Z_alpha)` is `2`-norm continuous and, by `(LT1)`,
its support trace is bounded by one fixed number strictly below `1/m`.
The proof of `stw22-finite-dimensional-trivial-field-traces`, applied to
the compact space `Z_alpha`, gives continuous weighted purifications

```text
w_(j,alpha)^*w_(j,alpha)=c|_(Z_alpha),
supp(w_(j,alpha)w_(j,alpha)^*)<=e_(j,alpha).            (LT3)
```

Indeed, this is exactly Michael selection for the multifunction treated in
`stw22-weighted-purification-all-sphere-fillings`; it uses only
`dim(Z_alpha)<=d` and the local product chart, not a global trivialization.

Regard `(LT3)` intrinsically as sections of the original bundle over
`Z_alpha`.  The section

```text
f_alpha^(1/2) w_(j,alpha)
```

extends by zero outside `Z_alpha`: its operator norm is at most
`f_alpha^(1/2)`, so it is in particular `2`-norm continuous across the
boundary.  This extension is independent of coordinates.  On overlaps a
transition automorphism carries `(LT2)--(LT3)` to the same intrinsic
section and preserves trace and orthogonality.

## Glue with colour cost only

For `0<=r<=d`, set

```text
v_(j,r)=sum_(colour(alpha)=r)
          f_alpha^(1/2) w_(j,alpha).                   (LT4)
```

The sum is a continuous global section.  Same-colour supports are
disjoint, so all cross terms in `(LT4)` vanish and

```text
sum_(r=0)^d v_(j,r)^*v_(j,r)=c             (1<=j<=m). (LT5)
```

At a fixed base point and for a fixed colour, at most one `alpha`
contributes.  For that `alpha`, the `m` range corners in `(LT2)` are
orthogonal.  Hence

```text
||sum_(j=1)^m v_(j,r)v_(j,r)^*||<=1,
||sum_(r=0)^d sum_(j=1)^m v_(j,r)v_(j,r)^*||<=d+1.    (LT6)
```

Notice that corners belonging to different charts or different colours
need not be compared.  This is exactly where the colouring absorbs the
`Aut(R)` cocycle.

If `sigma` is a bounded positive trace on `K_x/J_x`, `(LT5)--(LT6)` give

```text
m sigma(c)<=(d+1)||sigma||.                            (LT7)
```

Let `m` tend to infinity and then let `eta` decrease to zero.  Every
bounded positive trace on the gap vanishes.  Apply
`stw22-tracefree-fibre-gap-ideals-force-trace-continuity` to obtain the
integral description and uniform `2`-norm continuity of all traces.
