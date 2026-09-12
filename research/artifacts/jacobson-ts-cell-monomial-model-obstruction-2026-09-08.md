# The TS cell excludes every monomial natural-head model

2026-09-08. This is an exact obstruction to a specified class of linear
models of the strengthened Jacobson presentation. It does not establish
a norm-matrix gap or exclude arbitrary amenable marked quotients.

## 1. Statement and scope

Let `k` be any field of characteristic two. Let `M` be a nonzero vector
space with a specified basis, and let `Y` be another based vector space.
Finite and infinite algebraic dimensions are both allowed. Put

```text
V=(k^3 tensor M) direct-sum Y,
V_i=e_i tensor M,                 i=1,2,3.
```

Use the resulting basis of `V`. An invertible operator is **monomial**
if it sends every basis vector to a nonzero scalar multiple of a basis
vector. Thus monomial operators over `F_2` are precisely basis
permutations.

Let `G=GL_3(F_2)` and represent the finite packet `G_Q x G_P` on `V`.
Assume:

1. The head factor acts by its natural representation on `k^3`, tensored
   with `I_M`, and acts trivially on `Y`.
2. Every operator from the tail factor is monomial.
3. `H` is a monomial involution commuting with
   `K=GL(<e_1,e_3>)_Q`.

Retain the packet notation

```text
c=(I+E_13)_P,         z_Q=(I+E_23)_Q,
z_P=(I+E_23)_P,       z=z_Q z_P,
k_Q=(I+E_31)_Q,       k_P=(I+E_31)_P,
k=k_Q k_P,           b=(w_23,w_23).
```

Then the following two relations cannot both hold:

```text
(H b)^3=I,
W=[[H c H,k],H z H] z=I.                              (1)
```

Consequently there is no such representation of `Gamma_2` with nonzero
natural head. Over the ground field `F_2`, the stronger conclusion is
that `W!=I` already follows from assumptions 1--3: neither braid nor the
additional commutation `R=1` is needed.

The theorem allows arbitrary natural-head multiplicity, arbitrary
monomial tail action on that multiplicity, and an arbitrary head-trivial
complement. It is therefore not limited to seven rays or to a particular
choice of shifts. It does assume a natural head and a monomial `H`;
neither condition follows for general representations of `Gamma_2`.

## 2. The invariant blocks forced by the finite packet

Write the head root operators as `I+E_ij`, with each `E_ij` carrying
the identity on `M` and vanishing on `Y`. Since the tail commutes with
the head, it commutes with `E_ij` and with

```text
P_i=E_ij E_ji                         (j!=i),
```

the projection onto `V_i`. Thus every tail element preserves each
`V_i` and preserves `Y`.

Similarly, commuting with `K` implies commuting with `E_13,E_31`
and therefore with `P_1,P_3`. Put

```text
V_0=V_1 direct-sum V_3,
L=V_2 direct-sum Y.
```

Then `H` preserves `V_1,V_3,L`. All operators centralizing `K`
preserve these blocks. These statements use explicit projections and
do not require semisimplicity in characteristic two.

Let

```text
Z=z_Q-I : V_0 -> L,
J=H_L Z H_0^(-1),
A=H c H,
B=H z_P H.
```

Here `Z` vanishes on `V_1` and sends every basis vector `e_3 tensor m`
to `e_2 tensor m`. The suffixes indicate restrictions to `L,V_0`.
Since `H^2=I`,

```text
H z_Q H=I+J,
H z H=(I+J)B.                                        (2)
```

The operator `A` centralizes `K`. Hence `A` commutes with `k_Q`,
and `k_P` commutes with `k_Q` by the direct-product packet relation.
It follows that

```text
u:=[A,k]=[A,k_P].                                    (3)
```

In particular `u` and `B` are monomial and block diagonal for
`V=V_0 direct-sum L`. Both centralize `K`, so they also preserve
`V_3` separately inside `V_0`.

## 3. Extract the off-diagonal identity from W

For a block diagonal operator `g=(g_0,g_L)` and a map
`X:V_0 -> L`, write `(X,g)` for `(I+X)g`. These operators form the
semidirect product of the additive space `Hom(V_0,L)` with the
block diagonal invertible operators. Its action and multiplication are

```text
g.X = g_L X g_0^(-1),
(X,g)(Y,f)=(X+g.Y,gf).
```

In these coordinates a direct multiplication gives

```text
[(0,u),(J,B)]
  =(u.J-[u,B].J,[u,B]).                               (4)
```

The head and tail root involutions commute, so `z=z_Q z_P` is an
involution. Thus `W=I` is equivalent to the assertion that the
commutator on the left of (4) equals

```text
z=(Z,z_P).
```

Comparing its diagonal and off-diagonal entries gives

```text
[u,B]=z_P,
u.J-z_P.J=Z.                                         (5)
```

This identity is forced by the TS word itself. No commutation `R` or
tail braid has entered its derivation.

## 4. Basis support forces the contradiction

Fix a basis vector of `V_3`. Each of the maps `u.J` and `z_P.J`
sends it to one nonzero scalar multiple of a basis vector of `L`:
the diagonal maps preserve `V_3`, and every operator in the defining
composition of either map is monomial on the relevant basis. The right
side of (5) is one specified basis vector of `V_2`.

A difference of two nonzero scalar multiples of basis vectors can be
one nonzero multiple of a specified basis vector only if **both**
left-hand basis vectors equal that specified one. Indeed, distinct
left-hand supports cannot cancel, and a common different support
cannot produce the specified support. It follows that

```text
(z_P.J)(V_3) subset V_2.
```

Since `z_P` and `H_0` map the basis of `V_3` bijectively to itself,
the image on the left is

```text
(z_P.J)(V_3)=z_P(H_L(V_2)).
```

The tail preserves both `V_2` and `Y`. Therefore
`H_L(V_2) subset V_2`. Applying `H_L` once more and using `H_L^2=I`
shows equality. Thus `H` preserves all three coordinate blocks
`V_1,V_2,V_3`.

The tail factor of `b` also preserves these three blocks, while its
head factor `w_23` interchanges `V_2,V_3`. Hence `H b` interchanges
`V_2,V_3`, and its third power still interchanges them. Since these
are distinct nonzero direct summands, `(H b)^3` cannot be the identity.
This contradicts (1).

Over `F_2`, one can stop earlier: each nonzero scalar is one, and a
sum of two basis vectors is never a single basis vector. Thus (5)
itself is impossible over `F_2`, without invoking the first braid.

## 5. Consequence for the search and its limit

The amenable seven-ray construction is a special case with `k=F_2`,
`dim(M)=1`, a permutation tail and a permutation involution. The
obstruction rules out every replacement within the broader class
above, including arbitrary numbers of rays, arbitrary monomial
boundary changes, and arbitrary natural-head multiplicity.

A proposed amenable replacement can avoid this obstruction by allowing
linear combinations in `H`, changing the head representation, or
leaving this class of linear models. Those possibilities are not
settled here. In particular, characteristic-two basis support does not
supply any quantitative estimate for complex unitary matrices, nor
does it show that all norm-matrix-corona representations kill the
head. The MF status of `Gamma_2` remains unresolved.

The proof is a symbolic block-matrix calculation. No computational
experiment or formal proof checker is claimed.
