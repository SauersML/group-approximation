---
rg: 2
id: binary-native-selector-atom-hecke-proof
kind: route
title: Expand the marked character atom across the relative selector word
target: binary-native-selector-atom-hecke-dichotomy
requires:
  - finite-character-hecke-intersection-formula
---

Put `e=e_chi` and `u=g_1^(-1)g_2`.  From `(NSH4)`,

```text
S_1^*S_2S_2^*S_1=e u e u^(-1)e,
tau(S_1^*S_2S_2^*S_1)=||eue||_2^2.                   (NSHP1)
```

Expand both copies of the character idempotent:

```text
||eue||_2^2
 =|H|^(-2) sum_(h,k in H)
   chi(h)chi(k) tau(h u k u^(-1)).                    (NSHP2)
```

The canonical group trace keeps exactly the pairs satisfying
`h u k u^(-1)=1`.  Such pairs are parametrized by
`I=H intersect uHu^(-1)`.  Their signed sum is `|I|` if the two restricted
characters agree and is zero otherwise, by finite-character orthogonality.
This proves `(NSH5)`.

Also `tau(e)=1/|H|`.  Because both selector words centralize `z`, the
relative word `u` does as well, and `<z><=I`.  Therefore compatibility gives

```text
|I|/|H|^2 >=2/|H|^2=2^(-9)/|H|=2^(-9)tau(e),          (NSHP3)
```

which is `(NSH6)`.

All expressions in `(NSHP1)` are fixed group-algebra star-polynomials.
Finite-group normalized-HS exactification changes them by `o(1)`, and the
canonical trace conditions converge to their group-trace values.  This
gives the asserted robust form without any estimate involving the ambient
multiplicity dimension.
