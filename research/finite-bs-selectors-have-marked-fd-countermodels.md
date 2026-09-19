---
rg: 2
id: finite-bs-selectors-have-marked-fd-countermodels
kind: claim
title: Finite Bass--Serre nonlinear selector compilers have marked exact finite countermodels
distinct_from:
  one-bit-selector-cannot-orient-paired-frame-hard-cycle: That audits reuse of the selector sign inside one paired packet; this rules out every finite iteration of selector packets and finite-subgroup Reynolds edges before any packet-specific orientation is chosen.
  canonical-types-extend-every-finite-bass-serre-actor: That extends canonical ultraproduct types through finite Bass--Serre actors; this gives literal exact finite quotients retaining the marked sign and every named local packet.
  wagon-wheel-stops-before-bcs-groupification: That proves the affine boundary obstruction for local LCS fragments and audits the one-way wagon-wheel modulus; this applies to genuinely noncommuting finite selector groups as well.
---

**ESTABLISHED FIREWALL.**  Let `B` be any finite shared-variable BCS and let

```text
W_B=<J,x_v | J^2=x_v^2=1, [J,x_v]=1,
                 [x_v,x_w]=1 when v,w share a context>.       (FBS1)
```

Assume `J` is kept independent.  Starting from `W_B`, perform finitely many
of the following operations:

1. amalgamate a finite auxiliary group over one of the named finite context
   or selector subgroups;
2. add an HNN edge whose source and target are named finite subgroups; or
3. take a finite graph of such vertices and finite edge groups.

Call the resulting group `G`.  Then `G` is residually finite.  Moreover, for
every finite list of named finite packets there is a finite quotient

```text
phi:G->F                                                     (FBS2)
```

which is injective on every packet and satisfies `phi(J)!=1`.  Consequently
the finite-dimensional exact representation `lambda_F o phi` retains the
marked sector and the complete regular type vector of every named packet.

This applies in particular to the one-bit Clifford selector.  For a finite
abelian context packet `C` and a central involution `z in C`, its auxiliary
group

```text
K(C,z)=<C,p,q | p^2=q^2=1, [p,C]=[q,C]=1, [p,q]=z>             (FBS3)
```

is finite: every element has the form `c p^epsilon q^delta`, so
`|K(C,z)|<=4|C|`, and the twisted-product model proves that `C` embeds.
Thus adjoining all one-bit selectors is only amalgamation by finite vertex
groups.  Ordinary finite-subgroup Reynolds/HNN actuators remain within the
same class.

To prove the claim, `W_B` is a direct product of `C_2=<J>` with a
right-angled Coxeter group and is residually finite.  The standard finite-edge
Bass--Serre residual-finiteness lemma says that a finite graph of residually
finite vertex groups with finite edge groups has residually finite fundamental
group.  One direct proof quotients each vertex group so that the finitely many
edge groups and syllables in a chosen reduced normal form remain distinct;
the resulting finite graph of finite groups is virtually free and residually
finite, and its normal-form theorem preserves the chosen word.  Induction over
the finite construction gives residual finiteness of `G`.

For `(FBS2)`, apply residual finiteness to the finite set consisting of `J`
and every nonidentity element of every named packet, then take the product of
the finitely many separating quotients.  In the left regular representation
of `F`, restriction to a packet `H` is a multiple of `lambda_H`.  Therefore
each one-dimensional character atom has normalized trace `1/|H|`.  In
particular, for an injected central-sign context

```text
C_c=<J,x_v:v in X_c> ~= C_2^(|X_c|+1),
```

every assignment Reynolds atom has trace

```text
tr(P_(c,a)Q_-)=1/|C_c|>0.                               (FBS4)
```

The Clifford selector cuts it into two equal nonzero halves.

Hence no finite compiler built only from nonlinear finite selectors,
finite-subgroup Reynolds projections, and Bass--Serre transport can prove a
dimension-independent matrix theorem that collapses all forbidden atoms or
the marked sign: `(FBS2)--(FBS4)` are exact zero-defect countermodels.  This is
not the old affine-selector obstruction; the auxiliary packets may be fully
noncommutative.  The missing attachment must leave the finite-edge
Bass--Serre class.  It needs a genuinely payload-sensitive ordinary relator
or global two-cell whose matrix consequence is not satisfied by these marked
finite quotients.

Applying Slofstra's wagon-wheel embedding afterward does not repair this
front end.  Its bounded fillings transfer an approximate-radical modulus
already present in the source, whereas the source here has exact finite
representations separating `J`.  The constellation argument supplies no
reverse normalized-HS decoder from the nonlinear BCS gap.

DERIVATION
finite-bass-serre-selector-countermodel-proof
