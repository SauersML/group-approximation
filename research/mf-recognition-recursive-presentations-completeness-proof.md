---
rg: 2
id: mf-recognition-recursive-presentations-completeness-proof
kind: route
title: Kill successive free factors when new c.e. elements appear
target: mf-recognition-recursive-presentations-is-second-level-complete
requires:
  - finitely-presented-sofic-non-mf
  - mf-positive-controls
---

Fix a finitely presented non-MF group `E`.  On input an index `e` for a c.e.
set `W_e`, start with the countable free product

```text
*_(j>=0) E_j.
```

When the `(j+1)`st new distinct element enters `W_e`, enumerate relators
killing every generator of `E_j`.  The resulting recursive presentation
`H_e` is uniform in `e`.

If `W_e` is infinite, every free factor is eventually killed and `H_e=1`, so
`H_e` is MF.  If `|W_e|=k`, precisely the first `k` factors are killed and

```text
H_e ~= *_(j>=k) E_j.
```

The surviving `E_k` embeds, so subgroup heredity of MF makes `H_e` non-MF.
Thus

```text
e in FIN  iff H_e is non-MF,
e in INF  iff H_e is MF.
```

FIN and INF are respectively `Sigma^0_2`- and `Pi^0_2`-complete.  For the
upper bound, at scale `n` inspect only the first `n` relators of the recursive
stream and include in the certificate a later prefix index at which all
finite normal-closure derivations used at that scale are present.  This
preserves the `forall exists` form.
