---
rg: 2
id: kl-leavitt-identity-size-is-bounded-by-hs-escapes
kind: claim
title: Unitary almost-representations of the Leavitt units bound every Kervaire--Laudenbach identity from below
distinct_from:
  nonsingular-equations-preserve-matrix-certificates: that proves the old-relator cost inequality for any presented coefficient group; this fixes one finite presentation of the Leavitt unit group, so the inequality becomes a lower bound on every Leavitt identity at once.
  fp-simple-nonhyperlinearity-is-one-word-domination: that identifies nonhyperlinearity of a finitely presented simple group with a one-word energy domination; this reads the same kind of inequality in the opposite direction, as a size fence on algebraic certificates.
---

Fix a finite presentation `R^x = <S | R>`; one exists by
`leavitt-unit-group-finitely-presented`.  Let `w in R^x * <t>` be nonsingular
and let `1 != a in R^x` die in `(R^x * <t>)/<<w>>`.  Write the death as an
identity in `F(S) * <t>`,

```text
a = prod_(j=1..A+B) v_j f_j^(epsilon_j) v_j^(-1),     f_j in R or f_j = w,
```

with `A` factors from `R`.  Every such identity exists.  Relations of `R^x`
used in some other form are products of conjugates of `R`-relators, so
substituting them only changes `A`.  Then for every `d >= 1` and every
`U in U(d)^S`,

```text
||a(U) - I||_2  <=  A * max_(r in R) ||r(U) - I||_2.            (KS1)
```

Consequently a single tuple with relator defect `delta` and mark distance
`alpha = ||a(U) - I||_2` gives `A >= alpha / delta` for every identity that
kills `a`, whatever the equation.

## Use

The computational presentation is the atlas list `T_St` over `A_8 * A_8` of
`atlas-steinberg-rank-five-translation`.  It presents `St_5(L)`, and by
`leavitt-steinberg-map-iso-from-rank-three` and the prefix-code isomorphisms it
presents `R^x` itself.  The optimization probes of `leavitt-steinberg-hs-unstable`
produce exactly such tuples.  Each probe with small `T_St` defect and a far
atlas word is therefore also an explicit lower bound on the size of every
Kervaire--Laudenbach certificate over the Leavitt unit group.  A family with
defect tending to zero and a mark bounded away from `I` refutes every
certificate for that mark and selects the hyperlinear branch.
