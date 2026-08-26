# Shulman completion of the tensor-synchronized Higman rope

This note closes the one limitation isolated in
`regular-mf-tensor-synchronized-rope-gap-audit-2026-08-26.md`. The audit was
deliberately zero-literature: it proved the tensor model and then stopped at
compatible-corona HNN permanence. Shulman's current theorem supplies exactly
that last implication.

The external inputs are Shulman's arXiv:2603.13564v2, Theorem 20 (the
compatible-corona criterion for separable full amalgams), and Ueda's
universal-HNN full-corner construction.

## 1. Tensor synchronization gives the required corona datum

Let `G=Gamma times Q`, with `iota0(s)=(s,1)` and
`iota1(s)=(s,tau(s))`. Assume a regular operator-MF realization
`(A,rho,tr)` of `Gamma`, eventually separating finite quotients
`beta_n:Q->B_n`, and finite maps `lambda_n:Gamma->C_n` satisfying

```text
ker(lambda_n|S) <= ker(beta_n tau).                         (1)
```

In the finite image `G_n` of `(lambda_n,beta_n)`, the two edge maps

```text
s |-> (lambda_n(s),1),
s |-> (lambda_n(s),beta_n(tau(s)))
```

have equal kernels. Their restrictions in the left regular representation of
`G_n` are the same multiple of the regular representation of that finite
quotient of `S`. Hence a unitary `W_n` conjugates them exactly.

In

```text
E = product_n (A tensor M_|G_n|) / direct-sum_n (A tensor M_|G_n|)
```

put

```text
V(g,q)=[rho(g) tensor L_n(lambda_n(g),beta_n(q))]_n,
W=[1 tensor W_n]_n.
```

Then `V` is a group homomorphism and

```text
W V(iota0(s)) W^* = V(iota1(s)).                            (2)
```

The ultralimit of `tr tensor normalizedTrace` satisfies

```text
T(V(g,q)) = delta_((g,q),(1,1)).                            (3)
```

The first factor kills `g!=1`; eventual separation by `beta_n` kills `q!=1`
once `g=1`. Thus `V` is injective.

Every separable subalgebra of `E` is MF. For finitely many noncommutative
polynomials, quotient norms are limsups of coordinate norms. Choose one late
coordinate for each lower estimate and take their finite direct sum; all upper
estimates hold on a common tail. Each such finite direct sum of
`A tensor M_|G_n|` is MF, and diagonalization gives a matrix-corona embedding.
In particular `D'=C*(V(G),W)` is MF.

## 2. The compatible amalgam embeddings are faithful

Set

```text
D=C*(V(G)), B0=C*(V(iota0(S))), B1=C*(V(iota1(S))),
alpha=Ad(W)|B0:B0->B1.
```

Choose a faithful embedding `j:D'->Qmat` into a matrix corona. Ueda's corner
uses

```text
P = M_2(D) *_(B0 direct-sum B1) M_2(B0),                    (4)
```

where the edge enters the first factor by `(b0,b1)|->diag(b0,b1)` and the
second by `(b0,b1)|->diag(b0,alpha^-1(b1))`. Both factors embed faithfully
in `M_2(D')`:

```text
Phi1(X)=X,
Phi2(Y)=diag(1,W) Y diag(1,W)^*.
```

They agree on the edge because

```text
Phi2(diag(b0,alpha^-1(b1)))=diag(b0,b1)=Phi1(diag(b0,b1)).
```

After composing with the amplification of `j`, Shulman's Theorem 20 makes
`P` MF. MF passes to C-star subalgebras and corners, so Ueda's corner gives an
MF universal algebra `Hcal=HNN(D,B0,alpha)`.

This is the step missing from the zero-literature audit. Merely sending the
stable letter to `W` need not be faithful; Theorem 20 makes the **universal**
HNN algebra MF.

## 3. The abstract HNN group embeds

Let

```text
H=<G,t | t iota0(s) t^-1=iota1(s), s in S>.
```

The GNS representation of `(D,T)` restricts to `lambda_G` by `(3)`. The
restriction of `lambda_H` to `G` on `l2(H)` is a direct sum of copies of
`lambda_G`, so it extends to a representation of `D`. The unitary
`lambda_H(t)` implements `alpha` on `B0`; the universal property gives a
representation `Hcal->B(l2(H))` sending canonical group words to their left
regular unitaries. Since `lambda_H(h)delta_1=delta_h`, no nonidentity group
element dies. Thus `H` embeds in the unitary group of the MF algebra `Hcal`.
The regular character pulls back from `C*_r(H)`, so the realization is regular
operator-MF.

Consequently the tensor-synchronization hypotheses make the twisted Higman
rope regularly operator-MF. Combined with the finite graph models and the
Mikhailova witness, this closes the compiler's positive branch.
