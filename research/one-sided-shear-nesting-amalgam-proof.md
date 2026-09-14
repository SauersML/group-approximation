---
rg: 2
id: one-sided-shear-nesting-amalgam-proof
kind: route
title: Strip the shear algebraically, then compare one-sided ideals in finite quotients of the two-chart amalgam
target: one-sided-shear-conjugates-cannot-strictly-nest
requires: []
---

Complete direct proof.

**Lemma (one-sided chart nesting).** With `P, f` as in the target: if `f P = f`
then `P f = P`, and if `P f = f` then `f P = P`.

*Proof.* Put `L = K cap K'` and `U = K *_L K'`, with the natural map `q : U -> G`.
In `G` an equality `k'_1 k_1 = k'_2 k_2` (`k'_i in K'`, `k_i in K`) gives
`k'_2^-1 k'_1 = k_2 k_1^-1 in L`, and the same identification holds in `U`. So `q`
is injective on the product sets `K'K` and `KK'`, which contain `K union K'`. The
identity `f P = f` therefore lifts to `F_p[U]`. Put `X = P f - P in F_p[U]`.

The amalgam of two finite groups is virtually free, hence residually finite.
Choose a finite quotient `psi : U -> F` injective on `K union K' union supp X`.
In `F_p[F]`, `fbar Pbar = fbar` gives the left-ideal containment
`F_p[F] fbar <= F_p[F] Pbar`. For an idempotent `e` of a finite group algebra,
left and right multiplication by `e` on the regular module have the same rank:
both equal `|K|` times the identity coefficient of the `p`-adic idempotent lift.
Since `F_p[F]` is free over `F_p[psi K]`, the dimensions are
`dim F_p[F] Pbar = [F:K] dim P F_p[K]` and `dim F_p[F] fbar = [F:K'] dim f F_p[K']`.
Equal normalized ranks make them equal. So the two left ideals coincide,
`Pbar = y fbar` for some `y`, and `Pbar fbar = Pbar`. Thus `psi(X) = 0`, hence `X = 0`,
and `P f = P` in `S`. The second statement is the same argument on right
ideals. `square`

**Case 1** (`P N = 0`, `N P = N`). Left-multiply `D P = D` by `1-N`, the inverse of
`1+N`, to get `f(1-N)P = f(1-N)`. Because `N P = N`, this is
`f P - f N = f - f N`, so `f P = f`. The lemma gives `P f = P`. Then, using `P N = 0`,

```text
P D = P (1+N) f (1-N) = P f (1-N) = P (1-N) = P - P N = P.
```

So `P D = P` and `D P = D`: each lies in the left ideal of the other, and
`S D = S P`. If also `P D = D`, then `D = P D = P`.

**Case 2** (`P N = N`, `N P = 0`). Right-multiply `P D = D` by `1+N` to get
`P(1+N) f = (1+N) f`. Because `P N = N`, this is `P f + N f = f + N f`, so `P f = f`.
The lemma gives `f P = P`. Then, using `N P = 0`,

```text
D P = (1+N) f (1-N) P = (1+N) f P = (1+N) P = P + N P = P.
```

So `D P = P` and `P D = D`, whence `D S = P S`. If also `D P = D`, then `D = P`. `square`

A group element `g` in the conjugating unit is absorbed by replacing `f` with
`g f g^-1 in F_p[g K' g^-1]`.
