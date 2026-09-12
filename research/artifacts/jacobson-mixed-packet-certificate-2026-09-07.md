# An exact mixed packet below the defect-two threshold

2026-09-07. This is a finite algebraic certificate, not a proof of either
MF or non-MF for the joint Jacobson group. It sharpens the boundary of the
[two-braid reduction](jacobson-two-braid-reduction-2026-09-07.md).

There is an exact 12-dimensional representation of the finite packet
`F=GL_3(F_2)_Q x GL_3(F_2)_P` and an exact overlap-central involution
`H` such that the marked negative rank is eight and both braid defects
are strictly less than two. Consequently the multiplicity restriction
`rank_-(w)=8k` is attained with `k=1`, and the infimum `gamma` in that
reduction satisfies

```
0 <= gamma < 2.                                          (1)
```

This supplies no positive lower bound for `gamma`. In particular it
does not assert that either of the two braid relations is exact.

## Exact representation data

All computations take place in the degree-six field

```
E=Q[z]/(1+z+z^2+z^3+z^4+z^5+z^6),   z=exp(2*pi*i/7).
```

The polynomial is irreducible: after replacing its variable by `t+1`,
Eisenstein's criterion at seven applies. Thus a nonzero coefficient
vector in the basis `1,z,...,z^5` certifies a nonzero complex number in
the specified embedding. Complex conjugation sends `z` to `z^6`.

For the group `D=GL_3(F_2)` use the generators

```
x=[[0,0,1],[0,1,0],[1,0,0]],
y=[[1,0,0],[0,0,1],[0,1,1]].
```

Set `g=z+z^2+z^4-z^3-z^5-z^6`, so `g^2=-7`, and put

```
S_ij=(g/7)(z^(ij)-z^(-ij)),       1<=i,j<=3,
T=diag(z^4,z^2,z).
```

The assignments `rho(x)=S`, `rho(y)=S T` define an exact unitary
representation of `D`. This assertion has a finite exhaustive certificate
in [the replay program](../../experiments/jacobson_mixed_cyclotomic_certificate.py):
enumerate the 168 invertible binary matrices; check that `x,y` generate
them; assign the matrices `rho(a)` along a spanning set of positive-word
paths from the identity; and check **every** one of the 336 generator
edges

```
rho(x a)=S rho(a),       rho(y a)=S T rho(a).              (2)
```

The check uses exact rational coefficients in `E`. It also checks exact
unitarity of `S` and `S T`. To justify the certificate criterion, (2)
implies by induction that left multiplication by any word in `x,y`
has the assigned matrix product on every group element. Apply this at
the identity and at an arbitrary `a` to obtain
`rho(b a)=rho(b)rho(a)` for every `a,b`. Positive words suffice since
the two finite-order generators generate the group. Thus this finite
check proves the representation identity for all group elements; it is
not a sample of relations or a numerical approximate representation.

Let `K=GL(<e_1,e_3>)` as before, and let `chi` be its sign character:
it equals minus one at its three involutions and plus one elsewhere.
Define

```
P=(1/6) sum_(k in K) chi(k) rho(k).
```

This is the rank-one orthogonal projection onto the sign summand of the
restriction of `rho` to `K`. The certificate checks the character table
on all 36 products of `K`, `P*=P=P^2`, `Tr(P)=1`, and commutation with
each `rho(k)`.

## The involution and its two determinants

Use the exact packet representation

```
pi(a_Q,b_P)=rho(a) tensor (1 directSum rho(b)).
```

Let

```
A=[[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]],
C=[[0,0,1,0],[0,1,0,0],[1,0,0,0],[0,0,0,-1]],
H=P tensor A + (I-P) tensor C.                           (3)
```

Both `A` and `C` are self-adjoint involutions. The orthogonal projection
identities for `P` show directly that `H*=H` and `H^2=I`. Since `P`
commutes with `rho(K)`, `H` commutes with `pi(K)`. For
`w=(I+E_13)_Q`, exact evaluation gives `Tr(pi(w))=-4`. As `pi(w)` is an
involution on dimension 12, its negative eigenspace has dimension eight.

Write `B=pi(w_23,w_23)`, `D_0=pi(1,w_13)`. Exact Gaussian elimination
over `E` gives

```
det((H B)^3+I)
 = (4197249280 - 5752424288(z^2+z^5)
               -10925177600(z^3+z^4))/182284263,

det((H D_0)^3+I)
 = (160 - 288(z^2+z^5) - 448(z^3+z^4))/7.                (4)
```

Each displayed vector has degree at most five and a nonzero constant
coefficient, so irreducibility proves that both determinants are nonzero.
For any finite-dimensional unitary `V`, the spectral theorem gives

```
||V-I||<2  iff  -1 is not an eigenvalue of V
           iff  det(V+I)!=0.                             (5)
```

Apply (5) to the two unitary cubes in (4). This proves both strict
operator-norm bounds, the sharpness at marked rank eight, and (1).

## Replay and remaining question

Run

```
python3 experiments/jacobson_mixed_cyclotomic_certificate.py
```

The [committed result](jacobson-mixed-cyclotomic-replay-2026-09-07.json)
contains the exact coefficients in (4) and records the scope of the
certificate. The arithmetic uses rational numbers throughout; the
discovery search and floating-point eigenvalue estimates are not inputs
to its proof. Matrix inversion in the field is checked using the product
of the six Galois conjugates, and nonzero pivots are selected exactly.

The finite packet is admissible for the infimum, but does not establish a
zero infimum. A proof of the requested existence theorem by this route
still requires a positive lower bound for all admissible packet types
and all their multiplicities. Neither an unsuccessful search nor the
divisibility of a nonzero eigenspace supplies that bound.
