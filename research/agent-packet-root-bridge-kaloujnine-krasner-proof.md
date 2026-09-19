---
rg: 2
id: agent-packet-root-bridge-kaloujnine-krasner-proof
kind: route
title: Realize a perfect-kernel separator inside an alternating wreath bridge
target: agent-packet-root-bridge-is-perfect-kernel-separation
requires:
  - agent-packet-root-finite-detectors-are-normal-quotient-selectors
  - forbidden-character-kernel-quotient-compiler
  - agent-pk-affine-ghost-survives-quotient
---

Assume `(PKB2)` and put `L=<<z>>_Gamma` and `M=H intersect L`.  Then `M` is
normal in `H`.  Since `tilde pi(z)=1`, the representation kills `L`, hence
`M<=ker(pi|H)`.  The map `H/M -> Gamma/L` is injective.  Full group
`C^*`-algebras preserve subgroup inclusions, for example by induction of
unitary representations.  Therefore `q=0` in `C^*(Gamma/L)` implies that
its image is already zero in `C^*(H/M)=C[H/M]`.  This proves `(PKB3)`.

Conversely, assume `(PKB3)` and set `Q=H/M`.  The
Kaloujnine--Krasner embedding puts the finite extension `H` inside

```text
M wr Q,
```

with the wreath quotient restricting to the original map `H->Q` and with
`H` intersecting the base group in exactly `M`.  Embed the finite group `M`
in an alternating group `A_n`, with `n>=5`, and put

```text
K=A_n wr Q=(A_n)^Q semidirect Q.                       (PKP1)
```

This embeds `H` in `K`.  Let `z` be a three-cycle in the identity-coordinate
copy of `A_n`.  Simplicity of `A_n` and transitivity of the regular `Q`-shift
give

```text
<<z>>_K=(A_n)^Q,
K/<<z>>_K=Q,
H intersect <<z>>_K=M.                                (PKP2)
```

Form `Gamma=G *_H K`.  Bass--Serre normal form embeds both factors, so `G`
and the order-three element `z` survive.  Since `pi|H` kills `M`, it factors
through `Q`.  The representation of `K` obtained from `K->Q` agrees with
`pi|H`; the amalgam universal property therefore extends `pi` to
`tilde pi` with `tilde pi(z)=1`.

Killing `z` in the amalgam replaces `K` by `Q`, so

```text
Gamma/<<z>>_Gamma
  congruent G *_H Q
  congruent G/<<M>>_G.                                 (PKP3)
```

Because `q` is already zero in `C[Q]`, it is zero in this quotient.  The
finite-detector theorem applied to `H<=K` proves `(PKB5)`, and correction of
the fixed finite `K` packet proves its approximate normalized-HS form.

Finally, for finite abelian `H`, the group kernel of `pi|H` is

```text
M_max=intersection_(r in R) ker(r)=R^perp.             (PKP4)
```

A character idempotent `e_chi` dies in `C[H/M_max]` exactly when `chi` is
nontrivial on `M_max`, equivalently `chi notin (R^perp)^perp=span(R)`.
Restricting to the central-sign slice converts linear span into affine span,
proving `(PKB6)` and the final obstruction statement.
