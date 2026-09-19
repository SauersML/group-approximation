---
rg: 2
id: primitive-shell-sorted-matcher-is-one-phase-torus-proof
kind: route
title: Rank the primitive residues and absorb the right eigenvector phases
target: primitive-shell-sorted-matcher-is-one-phase-torus
requires: []
---

The positive integers below `q` which are prime to `3` are

```text
1,2,4,5,7,8,... .
```

The zero-based rank of a unit `u` in this list is `floor(2u/3)`, proving
that `(SPT1)` is a permutation of `Z/LZ`.  Multiplication by `2` advances
the exponent `a`.  Write `u_a=3t+r`, with `r in {1,2}`.  Before reducing
modulo `q`,

```text
floor(4u_a/3)
 =4t+1 =2f(a)+1,   if r=1,
 =4t+2 =2f(a),     if r=2.                           (1)
```

Subtracting `q` from `2u_a` subtracts exactly `2q/3=L` from its rank, so it
does not change `(1)` modulo `L`.  Also `f(a)` is even exactly in the first
case.  This proves `(SPT3)`.

Since `P^*e_a=e_(a+1)`, equations `(SPT2)--(SPT3)` give

```text
PBP^*e_a=omega^(f(a+1))e_a
        =omega^(2f(a)+1_(f(a) even))e_a.             (2)
```

Both parities occur.  Comparison with `B^2` proves `(SPT4)`.

The spectrum of the one-cycle permutation `P` is the set of all `L`-th
roots, once each.  The map `f` assigns these roots in increasing order to
the exponent coordinates, so an eigenbasis-to-coordinate unitary `H`
satisfies `HPH^*=B`.  Its rows are the Fourier eigenvectors of the cycle,
in the order prescribed by `f`, proving `(SPT6)`.

If another unitary `K` has `KPK^*=B`, then

```text
(K H^*) B = B (K H^*).
```

The spectrum of `B` is simple, so `K H^*` is diagonal.  This proves
`K=RH`.  Conversely every diagonal `R` commutes with `B`, and hence every
`RH` conjugates `P` to `B`.  A right phase `V in {P}'` satisfies
`H V H^* in {B}'`, which is diagonal, so it is already included in `R`.
This proves `(SPT5)` and the phase count.  Substitution gives `(SPT7)`.
