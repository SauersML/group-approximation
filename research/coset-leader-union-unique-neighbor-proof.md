---
rg: 2
id: coset-leader-union-unique-neighbor-proof
kind: route
title: Expand the union of all erased-syndrome coset leaders
target: soundness-unique-neighbors-give-erasure-cleaning
requires: []
---

Fix `E`.  For every attainable syndrome `beta in im(H) cap F_2^E`, use
`(SUN1)` to choose `s_beta` with

```text
H s_beta=beta,  wt(s_beta)<=a|E|,
```

and put `S=union_beta supp(s_beta)`.  Every unique-neighbor row of `S` lies
in `E`: if a row outside `E` met `S` only in coordinate `j`, choose a
`s_beta` containing `j`.  That row meets `supp(s_beta)` exactly once, so
`(Hs_beta)` is nonzero there, contradicting `supp(beta) subset E`.

It remains to put `S` in the expansion range.  If `|S|>=alpha L/2`, order
the representatives arbitrarily and take the first prefix union `U` whose
size reaches `alpha L/2`.  The last added support has size at most `a|E|`,
so `(SUN3)` gives

```text
alpha L/2 <= |U| < alpha L.
```

By `(SUN2)`, `U` has at least `gamma alpha L/2` unique-neighbor rows, all
in `E` by the preceding argument applied to this prefix union.  This
contradicts `(SUN3)`.  Hence `|S|<alpha L/2`, and applying `(SUN2)` directly
to `S` gives

```text
gamma|S| <= |E|.
```

Finally, any `x` with `supp(Hx) subset E` has syndrome `beta=Hx` in the
chosen family, and

```text
x=(x+s_beta)+s_beta in C+F_2^S.
```

This proves `(SUN4)`.
