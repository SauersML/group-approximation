---
rg: 2
id: hs-collapse-sign-twist-non-mf
kind: claim
title: An involutive HS-collapse mark admits a property-T-free non-MF sign-twist wrapper
distinct_from:
  central-sign-corona-obstruction: That criterion uses one-sided compression of a property-(T) subgroup to manufacture HS-triviality of a commutator before cutting to a central sign corner; this assumes the marked HS-collapse estimate as input and converts it to a norm-corona obstruction by one HNN trace flip, with no property (T), no commutant transport, and no Clifford witness.
  kleene-halting-mark-collapse-diagonal: That turns a HALT-survival/NONHALT-HS-collapse compiler directly into a nonhyperlinear group by testing the canonical trace; this turns any one already-instantiated involutive HS-collapse mark into a non-MF group by adjoining a fresh central sign and one stable letter.
---

Let

```text
Gamma=<S|R>
```

be finitely presented, let `w` be a word in `S` whose image in `Gamma` is a
nontrivial involution, and use normalized Hilbert--Schmidt norm

```text
||X||_(2,d)^2=(1/d)Tr(X*X).
```

Assume that there are constants

```text
delta>0,                alpha<sqrt(2)                         (HST1)
```

such that every finite-dimensional unitary tuple `U=(U_s)_(s in S)` with

```text
max_(r in R) ||r(U)-I||_(2,d)<delta                         (HST2)
```

satisfies

```text
||w(U)-I||_(2,d)<=alpha.                                    (HST3)
```

Adjoin a fresh involution `z`, central over `Gamma`, and a stable letter `a`,
and define

```text
Gamma^tw = < S,z,a |
               R,
               z^2=1,
               [z,s]=1             (s in S),
               [z,a]=1,
               a w a^-1 = z w >.                              (HST4)
```

Then:

1. the natural map `Gamma x <z> -> Gamma^tw` is injective, so `z!=1` in
   `Gamma^tw`;
2. every homomorphism from `Gamma^tw` to the unitary group of any norm matrix
   corona

   ```text
   product_n M_(d_n)(C) / directSum_n M_(d_n)(C)
   ```

   sends `z` to `1`;
3. consequently `Gamma^tw` is finitely presented and is not CDE/operator-MF.

The construction is effective from the finite presentation, the word `w`,
and the collapse constants.

## Why the constant is `sqrt(2)`

On a hypothetical nonzero `z=-1` spectral corner, the HNN relation in `(HST4)`
becomes

```text
A W A* ~= -W,                                                (HST5)
```

where `W=w(U)` and `A` is the stable-letter unitary.  Normalized trace is
conjugation invariant, so `(HST5)` forces `tr(W)->0`.  For every unitary `W`,

```text
||W-I||_2^2 = 2-2 Re tr(W),                                  (HST6)
```

and hence the same corner forces `||W-I||_2->sqrt(2)`, contradicting
`(HST3)`.  No positive-density estimate in the original matrix block is
needed: operator norm permits cutting to the nonzero central sign corner and
renormalizing by that corner's own rank.

The full coordinate proof, including projection lifting, corner polar
correction, and the HNN base-embedding argument, is
`hs-collapse-sign-twist-non-mf-proof`.
