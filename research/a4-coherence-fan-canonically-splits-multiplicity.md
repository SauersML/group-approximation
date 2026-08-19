---
rg: 2
id: a4-coherence-fan-canonically-splits-multiplicity
kind: claim
title: The A4 coherence fan canonically factors the three-dimensional block from all external multiplicity
---

In the notation of `a4-regular-three-way-coherence-transducer`, let

```text
R = R_0 + R_1 + R_2,
S = Q_+ - (E_0+E_1+E_2),
T_j = sqrt(3) S R_j.
```

Define a unitary

```text
W : R H -> C^3 tensor S H
```

by

```text
W x = |j> tensor T_j x       for x in R_j H.
```

Then `W` removes **all** local multiplicity freedom.  In this factorization the
A4 generators act as

```text
W rho(a) W^* = diag(1,omega,omega^2) tensor I_S,
W rho(b) W^* = B tensor I_S,
```

where

```text
B_jj = -1/3,
B_jk =  2/3  for j != k.
```

Equivalently `B=(2/3)J-I_3`, with `J` the all-ones matrix.  This is a fixed
three-dimensional irreducible model of A4, while the whole growing part is the
single multiplicity space `S H` of relative dimension `1/4`.

Thus every exact regular A4 context in the normalized atlas network comes with
a **canonical compiler to one fixed 3-state quantum register tensored with a
multiplicity wire**.  Context-to-context freedom can be pushed entirely onto
maps between the multiplicity wires; it does not remain entangled with the
local A4 representation matrices.