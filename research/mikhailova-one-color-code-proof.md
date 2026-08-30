---
rg: 2
id: mikhailova-one-color-code-proof
kind: route
title: Collapse a transitive GKP embedding to the color of one basepoint
target: mikhailova-left-right-soficity-is-one-color-code
requires:
  - mikhailova-left-right-action-current-frontier
---

Write `G=F_m x F_m`, `M=M_H`, and identify `H` with `G/M` using
the coset of the identity as basepoint.

## From orbit charts to one color

Assume the action is sofic.  GKP Proposition 2.9 supplies a free
ultrafilter `U`, a homomorphism

```text
Phi:G->S_U,
```

and an equivariant isometric map `Pi:G/M->X_U`.  Put `c=Pi(M)`.
For every `g in G`,

```text
S_U(Phi(g))c=Pi(gM).
```

If `g in M`, the right side is `c`.  If `g notin M`, the two cosets
are distinct and the defining metric separation in Proposition 2.9 gives
distance one.  This is exactly `(MCC2)`.

## From one color back to every chart

Conversely, assume `(MCC2)` and define

```text
Pi(gM)=S_U(Phi(g))c.                                   (MCP1)
```

This is well defined.  If `gM=hM`, then `h^(-1)g in M`, so the two
values in `(MCP1)` have distance

```text
d_U(c,S_U(Phi(h^(-1)g))c)=0.
```

If the cosets are distinct, the same computation and `(MCC2)` give
distance one.  Thus `Pi` is isometric.  It is equivariant because
`Phi` is a homomorphism and `S_U` is an action.  GKP Proposition 2.9
now gives soficity of `G` acting on `G/M`.

This argument works for every transitive action: its entire GKP map is the
orbit of the image of one basepoint, and the stabilizer is read by the
zero/one displacement coefficient of that point.

## Finite color normal form

Represent `c` by colorings `c_n:A_n->N`.  Restrict `Phi` to the two
free factors.  Choose representative permutations for the images of a free
basis and extend them, using freeness, to exact homomorphisms

```text
sigma_n,tau_n:F_m->Sym(A_n).
```

Because the two factor images commute in `S_U`, for every fixed
`u,v in F_m`,

```text
d_H(sigma_n(u)tau_n(v),tau_n(v)sigma_n(u))->0.          (MCP2)
```

The universal action is precomposition by inverse.  Therefore `(MCC2)`
is precisely the agreement formula `(MCC3)`.  Conversely, `(MCP2)`
makes

```text
Phi(u,v)=[sigma_n(u)tau_n(v)]_U
```

a homomorphism `F_m x F_m->S_U`, and `(MCC3)` gives `(MCC2)`.
This proves the finite normal form.

## The exact quotient gate

Let `N=ker(q)`.  If `Phi(n,1)=1` for all `n in N`, then

```text
theta:H->S_U,       theta(q(u))=Phi(u,1)
```

is a well-defined homomorphism.  If `q(u) != 1`, then `(u,1) notin M`,
and `(MCC2)` gives

```text
d_U(c,S_U(theta(q(u)))c)=1.
```

Hence `theta(q(u)) != 1`, so `theta` is injective and `H` is sofic.
For a nonsofic `H`, a hypothetical color-code witness must therefore keep
some element of each coordinate kernel nontrivial as a permutation while
making it invisible to the single color orbit.  This is why quotient
descent and levelwise correction are exactly the missing steps, not
consequences of the GKP charts.
