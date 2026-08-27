# The first extension collision of the 24-dimensional Kassel omega packet

Start with the exact marked model of
`kassel-four-cell-has-exact-omega-model`.  On
`H=C^4 tensor C^6` it has

```text
x_alpha           = P_a tensor X,
x_beta            = P_b tensor I,
x_(-alpha)        = P_A tensor I,
x_(-beta)         = nu I,
x_(-(alpha+beta)) = I tensor Z,
```

where

```text
a=(2 3), b=(0 2)(1 3), A=(1 3 2),
nu=exp(-pi i/6), q=nu^(-2), [X,Z]=qI.
```

Write `D=x_(-(2alpha+beta))`, the one root generator left unused by the
four-cell.

## Either new relation extends exactly

Kassel (2.7) is

```text
[x_alpha,D] = x_(-beta) x_(-(alpha+beta))^(-1)
            = nu I tensor Z^(-1).                        (R7)
```

It has an exact solution `D=I tensor D_0`, with `D_0` diagonal.  If
`D_0 e_j=t_j e_j`, set

```text
t_j = nu^(-j) q^(-j(j+1)/2),       0 <= j <= 5.
```

Then `t_(j-1)/t_j=nu q^j`, including the cyclic equation at `j=0`
because `nu` has order twelve and `q=nu^(-2)`.  Hence
`[X,D_0]=nu Z^(-1)`.

Kassel (2.8) is

```text
[x_beta,x_(-(alpha+beta))]
 = x_(-alpha) D.                                      (R8)
```

Its left side is exactly one in this tensor packet, so (2.8) alone extends
exactly by `D=P_A^(-1) tensor I`.  Both one-face extensions retain
`w_beta^4=omega I`.

## The two faces collide on this packet

For an arbitrary unitary `D`, put

```text
epsilon_7 = ||[P_a tensor X,D] - nu I tensor Z^(-1)||_2,
epsilon_8 = ||(P_A tensor I)D-I||_2.
```

Because `[P_b tensor I,I tensor Z]=I`, these are exactly the normalized-HS
defects of (2.7) and (2.8), up to harmless multiplication by unitaries.
The second equality gives

```text
epsilon_8 = ||D-P_A^(-1) tensor I||_2.
```

The commutator map is `2`-Lipschitz in its second unitary variable, so

```text
||[P_a tensor X,D]-[P_a tensor X,P_A^(-1) tensor I]||_2
 <= 2 epsilon_8.                                      (L)
```

Direct permutation multiplication gives

```text
[a,A^(-1)] = A^(-1) = (1 2 3).
```

This permutation fixes exactly one of four points, whereas
`tr_6(nu Z^(-1))=0`.  Therefore the two target unitaries are trace-orthogonal:

```text
||(P_A^(-1) tensor I) - (nu I tensor Z^(-1))||_2^2 = 2.
```

The triangle inequality and `(L)` yield

```text
epsilon_7 + 2 epsilon_8 >= sqrt(2),
epsilon_7^2 + epsilon_8^2 >= 2/5.                       (G)
```

Thus (2.7) and (2.8) are the first cumulative extension pair that charges
the explicit omega packet.  Each face separately has zero energy, so the
pair is support-minimal for this model.

## Scope

`(G)` is a dimension-free inequality after amplifying this fixed packet, but
it is **not** a universal inequality over arbitrary representations of the
six-relator presentation.  Retuning the original four-cell generators could
still evade it.  The calculation identifies the first required coupling:
(2.7) puts the missing negative-long-root generator into the six-clock,
while (2.8) simultaneously identifies it with the four-point permutation
transport.  A global proof must show that every nontrivial marked model
contains a quantitatively comparable collision.

