---
rg: 2
id: toeplitz-finite-head-extension-preserves-root
kind: claim
title: A finite-head Toeplitz quotient preserves the marked defect root
distinct_from:
  schur-toeplitz-root-mark-is-fd-invisible: that kills the marked root in every exact finite-dimensional representation of the full group; the present infinite quotient preserves the root and isolates the additional approximation theorem a countermodel would require.
  toeplitz-defect-idempotents-do-not-localize-root-characters: that constructs an unconstrained additive character detecting all defect sites; this realizes the complete packet-headed Toeplitz and ascending-HNN relations in one concrete infinite quotient.
  hs-schur-toeplitz-root-defect-collapse: that asks for normalized-HS collapse of the root; this is an exact stress model, not an ultraproduct countermodel.
---

Let `A=k[B_f]`, `P=P_f`, `R_f`, `epsilon`, `sigma`, `H_f`, and
`w_f=x_12(P)` be as in the Schur--Toeplitz construction.  There is a
countable ring quotient

```text
eta:R_f -> T
```

and an injective endomorphism `beta:T->T` satisfying

```text
beta eta=eta sigma,                    eta(P)!=0,          (FTQ1)
```

such that the ascending HNN group

```text
K=<EL_5(T),s | sgs^-1=beta(g), g in EL_5(T)>              (FTQ2)
```

contains the nontrivial root `x_12(eta(P))`.  Consequently the natural
homomorphism

```text
H_f -> K
```

sends `w_f` to a nonidentity element.

Here is the construction.  Since `k` has odd characteristic and splits the
finite `2`-group packet, `A` is semisimple.  The augmentation `epsilon|_A`
is an allowed simple and kills `P`.  Form a faithful countable `A`-module
`V` by taking infinitely many copies of this one-dimensional augmentation
module and one copy of every other simple module.  Then

```text
0<dim_k(PV)<infinity,
a-epsilon(a)1_V is a finite-support matrix for every a in A.             (FTQ3)
```

Choose a basis with `PV` first and an isomorphism
`X:V->(1-P)V` equal to a unilateral shift by `r=dim(PV)` in that basis.
Let `Y` be its inverse on `(1-P)V` and zero on `PV`.  Thus

```text
YX=1,                     XY=1-P.                         (FTQ4)
```

The resulting representation of `R_f` has image `T`.  If `F` is the ring
of finite-support matrices on `V`, the symbol map gives an exact sequence

```text
0 -> T intersect F -> T -> k[z,z^-1] -> 0,                (FTQ5)
```

where `X->z`, `Y->z^-1`, and `a->epsilon(a)`.  In particular the augmentation
of an element of `T` is evaluation of its Laurent symbol at `z=1`.  Hence

```text
beta(c)=XcY+epsilon(c)P                                   (FTQ6)
```

is well defined on `T`, is unital and multiplicative, and obeys
`Y beta(c) X=c`; it is injective and proves `(FTQ1)`.

Put `G=EL_5(T)`.  The kernel of the symbol homomorphism from `G` is contained
in the finitary general linear group on `V^5`, hence is locally finite over
the finite field `k`.  The symbol image is a subgroup of
`EL_5(k[z,z^-1])`, which is residually finite: a nonzero Laurent-polynomial
matrix entry survives evaluation in some finite extension of `k`.  Thus `G`
is locally-finite-by-residually-finite.

Because `beta` is injective, `(FTQ2)` is

```text
(direct_limit(G,beta)) semidirect Z.
```

Finally, `eta(P)` is the nonzero finite-rank projection onto `PV`, so
`x_12(eta(P))!=1` in `EL_5(T)` and remains nontrivial in the ascending HNN
extension.

This does **not** refute normalized-HS collapse.  The permanence implication

```text
amenable normal subgroup + sofic quotient => sofic group
```

is not known in this direction; the standard closure theorem has amenable
**quotient**.  Therefore locally-finite-by-residually-finite does not certify
that `G`, its direct limit, or `(FTQ2)` is sofic.  A genuine countermodel must
add a direct LEF/sofic approximation of `(FTQ2)` which preserves
`x_12(eta(P))`.  Exact finite-dimensional representations cannot do so by
`schur-toeplitz-root-mark-is-fd-invisible`.

The construction nevertheless rules out any purely algebraic argument that
the complete Toeplitz and Steinberg relations kill the root.  It also
identifies a sharp falsification target for a proposed inequality

```text
||phi(w_f)-1||_2 <= omega(presentation defect)
```

because a direct LEF/sofic approximation of the finite-head HNN group
retaining the root would violate that inequality.  Until such an
approximation is proved, both the universal and canonical-trace versions of
the root-collapse problem remain open.
