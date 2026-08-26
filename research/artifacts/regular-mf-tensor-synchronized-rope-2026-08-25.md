# Tensor synchronization for the twisted Higman rope

This note proves that finite edge models do not have to separate the whole
first rope group.  They may be tensored with an independent regular-MF model
which supplies faithfulness while appearing identically on both edge maps.

## 1. Hypotheses and finite edge conjugacy

Let `(A,rho,tr)` be a regular operator-MF realization of `Gamma`: `A` is a
separable unital MF algebra, `rho:Gamma->U(A)` is injective, and

```text
tr(rho(g)) = delta_(g,1).                                      (1)
```

Let `beta_n:Q->B_n` be eventually separating finite quotients, and suppose
finite homomorphisms `lambda_n:Gamma->C_n` satisfy

```text
ker(lambda_n|S) <= ker(beta_n tau).                            (2)
```

Put `G_n` equal to the image of

```text
Gamma times Q -> C_n times B_n,
(g,q) |-> (lambda_n(g),beta_n(q)).                             (3)
```

Let `L_n` be its left regular representation.  The edge maps into `G_n` are

```text
kappa_(0,n)(s)=(lambda_n(s),1),
kappa_(1,n)(s)=(lambda_n(s),beta_n(tau(s))).                   (4)
```

The second kernel is automatically contained in the first, and `(2)` gives
the reverse inclusion.  Thus the two finite images of `S` are isomorphic.
The restrictions of the left regular representation of `G_n` to them are
equal multiples of their regular representations, so there is a unitary
`W_n` with

```text
W_n L_n(kappa_(0,n)(s)) W_n^* = L_n(kappa_(1,n)(s))            (5)
```

for every `s`.

## 2. The A-valued reduced-product model

Put

```text
E=product_n (A tensor M_|G_n|) / direct-sum_n (A tensor M_|G_n|)
```

and define

```text
V(g,q)=[rho(g) tensor L_n(lambda_n(g),beta_n(q))]_n.            (6)
```

Every coordinate is an exact representation, so `(6)` defines a homomorphism
of `Gamma times Q` into `U(E)`.  Equation `(5)` and the common `rho(s)` factor
give, for `W=[1 tensor W_n]_n`,

```text
W V(s,1) W^* = V(s,tau(s))                                    (7)
```

exactly.

Fix a free ultrafilter and define on `E`

```text
T([a_n])=lim_omega (tr tensor normalized-trace)(a_n).
```

This is well defined because the direct-sum ideal is in its kernel.  If
`g!=1`, the first tensor factor in `(6)` has trace zero by `(1)`.  If `g=1`
and `q!=1`, eventual separation by `beta_n` makes the left regular trace of
`(1,beta_n(q))` eventually zero.  Hence

```text
T(V(g,q))=delta_((g,q),(1,1)).                                 (8)
```

In particular the reduced-product homomorphism is injective.

Let `D'=C*(V(Gamma times Q),W)<=E`.  This separable algebra is MF.  Indeed,
given finitely many noncommutative *-polynomials in a finite tuple of elements,
the quotient norms are limsups of coordinate norms.  For each polynomial,
choose a sufficiently late coordinate giving its required lower estimate and
take the direct sum of all those coordinate tuples.  The direct-sum norm gives
every lower estimate, while choosing all coordinates late gives every upper
estimate.  This finite direct sum of algebras `A tensor M_|G_n|` is MF, so it
has the required matrix model.  Diagonalizing over finite polynomial
sets and rational tolerances embeds `D'` into a matrix corona.  The same
argument proves that every separable subalgebra of `E` is MF.

## 3. The C-star HNN and the group normal form

Let `D=C*(V(Gamma times Q))<=D'`, and let `B_0,B_1` be the two edge
subalgebras.  The unitary `W in D'` conjugates `B_0` onto `B_1`.  Embed `D'`
into a matrix corona; the edge conjugacy remains exact there.

Ueda's universal-HNN construction realizes the universal C-star HNN algebra
as a full corner of

```text
M_2(D) *_(B_0 direct-sum B_1) M_2(B_0).                        (9)
```

The embeddings of the two factors into the matrix corona agree on the amalgam
because of `(7)`.  Shulman's compatible-corona criterion makes `(9)`, and
hence its full corner, MF.

It remains to know that the abstract group HNN has not collapsed in this
C-star algebra.  The trace in `(8)` completes `D` to the group von Neumann
algebra of `Gamma times Q`; its conditional expectations onto the two edge von
Neumann algebras kill every group unitary outside the corresponding edge
subgroup.  The reduced von Neumann HNN normal form therefore assigns trace zero
to every nonidentity Britton-reduced group word.  Mapping the universal C-star
HNN algebra to this reduced von Neumann HNN shows simultaneously that all such
words survive and that the regular character pulls back to the MF algebra.
This proves regular operator-MF realization of the twisted rope.

## 4. Why an ignored witness factor is harmless

Suppose the benign overgroup is a product `K_0 times K_graph`, and the maps
`lambda_n` kill `K_0`.  A finite quotient of the whole first rope group would
then lose `K_0`, which is why the earlier profinite-synchronization theorem
could not use these maps.  In `(6)`, however, the `rho(g)` factor is a faithful
regular model of the whole first rope group, including `K_0`.  The finite
factor has only one job: make the two edge restrictions conjugate.  Tensoring
lets those two jobs coexist in operator norm with no dilution argument.

This is precisely what permits the regular-MF Mikhailova witness to be
intersected with the fixed finite-CEP graph witness.  The Mikhailova factor
retains the exact recursive kernel and the graph factor supplies compatibility;
neither factor is asked to do both.
