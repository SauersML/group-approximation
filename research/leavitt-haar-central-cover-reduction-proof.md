---
rg: 2
id: leavitt-haar-central-cover-reduction-proof
kind: route
title: Diracize the Haar row and isolate the surviving infinite Steinberg centre
target: leavitt-haar-mf-is-central-cover-regular-mf
requires:
  - character-diracization-limit
  - binary-leavitt-elementary-group-is-simple
  - leavitt-regular-character-is-not-mf
  - regular-mf-descends-finite-normal-quotients
  - thom-central-corner-criterion
---

Let `chi` satisfy the Haar-row condition and put `K` as in `(LCM1)`.
The scalar-kernel computation in `character-diracization-limit` makes `K`
normal.  Since `chi(v)=0` for every `1!=v in N`,

```text
K intersect N={1}.                                      (LCR1)
```

Conjugate tensor powers of an MF character are MF, and a diagonal choice of
the tensor exponent and matrix coordinate preserves operator-norm
multiplicativity.  Diracization therefore shows that `1_K` is an MF
character.  Equivalently, the regular character of `Delta/K` is MF.

It remains to locate `K`.  In rank twenty the canonical Steinberg kernel
`Z` is central, `Delta` is perfect, and `H=Delta/Z` is nontrivial simple.
The image `pi(K)` is normal in `H`.  If it were nontrivial, simplicity would
give `KZ=Delta`, so

```text
Delta/K = KZ/K = Z/(K intersect Z)
```

would be abelian.  It is also a quotient of the perfect group `Delta`, hence
perfect, and would therefore be trivial.  This would say `K=Delta`, contrary
to `(LCR1)` because `N` is nontrivial.  Thus `pi(K)={1}` and

```text
K <= Z.                                                  (LCR2)
```

If `Z/K` were finite, apply
`regular-mf-descends-finite-normal-quotients` to

```text
1 -> Z/K -> Delta/K -> H -> 1.
```

It would make `delta_H` MF, contradicting the established
`leavitt-regular-character-is-not-mf`.  Hence `Z/K` is infinite.  The same
regular MF model makes `Delta/K` hyperlinear, and Thom's central-quotient
descent makes `H` hyperlinear.

Conversely, suppose `K <= Z` and `delta_(Delta/K)` is MF.  The Steinberg map
is injective on `N`: its elementary-matrix image records every row (or
column) coefficient, so `N intersect Z={1}`.  Therefore `N intersect K={1}`.
Pulling `delta_(Delta/K)` back along `Delta -> Delta/K` gives an MF character
whose value on every `1!=v in N` is zero.  This proves the converse and the
equivalence.
