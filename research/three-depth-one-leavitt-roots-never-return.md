---
rg: 2
id: three-depth-one-leavitt-roots-never-return
kind: claim
title: Three individually nonnormal depth-one Leavitt roots never return to the signed Hecke pair
artifacts:
  - experiments/depth_one_triple_leavitt_return_search.py
  - research/three-depth-one-leavitt-return-enumeration.md
distinct_from:
  two-depth-one-leavitt-roots-return-only-constantly: that classifies two-factor products; this exhausts the first genuinely open three-factor search.
  asymmetric-depth-two-fold-return-retains-external-gauge: that constructs a depth-two three-leaf additive return equal to one constant external root; this excludes three successive depth-one root occurrences in arbitrary root channels.
  el20-six-moving-coefficient-square-bridges: that asks for a full coefficient bridge and remains open beyond the search radius excluded here.
---

Let

```text
M_1={s_mu t_nu: mu,nu in {empty,0,1}} minus {1}
```

be the eight nonconstant depth-one coefficients in the binary Leavitt
algebra, and let `X` be the `304` elementary roots on the seven actor
coordinates which individually do not normalize the signed Hecke pair
`(L_0,lambda_0)`.

Then no ordered triple of roots from `X` normalizes the signed Hecke pair:

```text
x,y,z in X  ==>  xyz notin Norm(L_0,lambda_0).          (DTR8)
```

This exhausts all

```text
304^3=28,094,464
```

ordered triples.  The first two factors have exactly `54,897` distinct
matrices in the faithful binary-prefix normal form, so it is enough to test
those exact pair products against all `304` possible third roots.  No
probabilistic, floating-point, finite-quotient, or bounded-depth evaluation is
used.

The exact normalizer test conjugates all ten signed generators of `L_0` and
requires every entry to reduce to `0` or `1`, the resulting constant matrix
to lie in the `8,192`-element group `L_0`, and its character sign to agree.
An exact support filter accelerates but does not weaken the search:
conjugating by `x_ab(c)` changes only row `a` and column `b`, so a nonconstant
entry outside that cross cannot possibly be removed by the proposed third
root.  The surviving candidate totals after the chosen generator order are

```text
4,181,384; 2,335,930; 1,099,624; 253,920;
23,736; 23,736; 6,130; 0.
```

Thus the eighth checked signed generator already eliminates the last
candidate; the remaining two generators are vacuous.

Consequently the smallest unresolved native EL20 return cannot consist of
three individually nonnormal depth-one elementary roots.  It must use a
normalizer-dressed reduction of a different type, at least four nonnormal
occurrences, or genuinely depth-two coefficient data.  This is a search
fence, not the Property-`(T)`-free MF collapse itself.

**ESTABLISHED 2026-08-30** by
[[three-depth-one-leavitt-return-enumeration]].
