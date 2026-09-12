---
rg: 2
id: abelianized-cover-self-centralizing-proof
kind: route
title: The crossed-word derivation sends the dummy commutator to g minus one
target: abelianized-cover-kernel-is-self-centralizing
requires: []
artifacts:
  - research/artifacts/conjugation-image-obstruction-and-self-centralizing-kernel-2026-09-08.md
---

## Proof

Let `Z[G]` be the free abelian group on `G` with `G` acting by left
translation, and define `D : F -> Z[G]` on generators by

```text
D(x) = 0  (x in X),      D(z) = 1,
```
extended by the crossed rule `D(uv) = D(u) + q(u)D(v)` and
`D(s^-1) = -q(s)^-1 D(s)`.  This is well defined on free words: deleting an
adjacent inverse pair leaves the value unchanged, by the two displayed rules.

On `R` the rule degenerates to `D(uv) = D(u) + D(v)`, since `q(u) = 1`, so
`D|_R` is a homomorphism into an abelian group and therefore kills `[R,R]`.
Consequently `D` descends to a well-defined map on the classes of elements of
`R` in `E`, and in particular is constant on `[R,R]`-cosets inside `R`.

For any `f in F` with `g = q(f)`, apply the rule from the left three times,
using `q(z) = 1`:

```text
D(f^-1 z^-1)     = D(f^-1) + q(f^-1)D(z^-1)
                 = -g^-1 D(f) - g^-1,
D(z f^-1 z^-1)   = D(z) + q(z)D(f^-1 z^-1)
                 = 1 - g^-1 D(f) - g^-1,
D(f z f^-1 z^-1) = D(f) + g D(z f^-1 z^-1)
                 = D(f) + g - D(f) - 1,
```
so

```text
D(f z f^-1 z^-1) = g - 1.                                            (1)
```

The commutator `f z f^-1 z^-1` lies in `R`, because `q(z) = 1`.  If `g != 1`
then `g - 1` is a nonzero element of the free abelian group `Z[G]`, so the
commutator is **not** in `[R,R]`, i.e.

```text
[fbar, zbar] != 1   in E,   for every g = q(f) != 1.                 (2)
```

This is the computation recorded in
`free-abelianized-cover-has-nontrivial-fd-radical`, there stated only for `g`
in the finite residual; it is four lines and presentation-independent, so it
is reproved here at the generality needed rather than by widening that node.

## Conclusion

`q(z) = 1` puts `z` in `R`, so `zbar` lies in `A_E = R/[R,R]`.  Let
`ebar in C_E(A_E)`.  Then `ebar` commutes with `zbar`, so by `(2)` its image
`g` in `G = E/A_E` must be `1`, i.e. `ebar in A_E`.  Conversely `A_E` is
abelian, so `A_E <= C_E(A_E)`.  This gives `(SC1)`, and `(SC2)` is the
resulting isomorphism `E/A_E = G`.
