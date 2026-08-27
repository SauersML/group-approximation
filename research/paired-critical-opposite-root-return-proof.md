---
rg: 2
id: paired-critical-opposite-root-return-proof
kind: route
title: Add the two opposite-root coefficients and conjugate the critical Hecke transvection
target: paired-critical-opposite-roots-return-only-trivially
requires:
  - one-nonnormal-dressing-cannot-preserve-moving-full-gram
  - fano-semidir-bridges-are-wrong-subgroup-or-gauged
---

Use the standard elementary matrices on the ordered coordinates `(2,8)`:

```text
d=x_28(1)=[[1,1],[0,1]],
x_82(c)  =[[1,0],[c,1]].
```

Characteristic two makes `x_82(c)^(-1)=x_82(c)`, and direct
multiplication gives

```text
x_82(c)d x_82(c)^(-1)
  =[[1+c,1],[c^2,1+c]].                                  (PRP1)
```

For two letters in the same root subgroup, the Steinberg root-additivity
relation is exact:

```text
x_82(b)x_82(a)=x_82(a+b).                                (PRP2)
```

Suppose the product normalizes the signed Hecke Reynolds atom.  Its actor
support must normalize the constant subgroup `L_0`, so `(PRP1)` belongs to
`L_0`.  Since `L_0` consists of matrices with entries in the embedded
constant field `F_2`, the diagonal entry `1+c` forces `c` to be a scalar,
and injectivity of `F_2 -> R` gives `c=0` or `1`.

The case `c=1` yields the `(2,8)` swap.  It is excluded by the same fixed
vector test used for the one-letter obstruction: the directed generating
list for `L_0` has no source coordinate `2`, so all its generators and all
of `L_0` fix `e_2`; the swap does not.  Therefore `c=0`.  By `(PRP2)` the
two relative letters multiply to the identity.  Consequently their
reservoir action is also the identity in every functorial word model, so
this return cannot compensate the nontrivial reservoir involution carried
by the Whitehead bridge.

The proof only fences the rank-one word `x_82(b)x_82(a)`.  The next search
must use unequal root channels or at least one intervening coefficient
word; neither is simplified by `(PRP2)`.

