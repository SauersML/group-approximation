---
rg: 2
id: scaling-unimodular-racg-blocks-proof
kind: route
title: Compute primitive differences and retain the graph-Clifford block
target: scaling-unimodular-racg-blocks
requires:
  - literal-base-presentation-complete
artifacts:
  - research/artifacts/composite-scaling-kazhdan-radical-reconstruction-2026-08-30.md
---

Fix `m>=2`.  The affine-base identification gives

```text
B=Z^3 semidirect SL_3(Z),
V_m=(Z[1/m]^3 semidirect SL_3(Z)) semidirect <t>.
```

As in the literal block calculation, sites at height `n` are represented by

```text
Z[1/m]^3 / m^n Z^3.
```

The marked ordered pair at that height has difference `m^(n-1)e_1`.
The first columns of matrices in `SL_3(Z)`, reduced modulo `m`, are
exactly the unimodular columns of `(Z/mZ)^3`.  Indeed reduction
`SL_3(Z)->SL_3(Z/mZ)` is onto, and over `Z/mZ` a unimodular column
extends to an invertible matrix; multiplying a second column by the inverse
determinant makes the completion special linear.  Thus the orbit differences
are precisely

```text
m^(n-1) u modulo m^n Z^3,   u unimodular modulo m.       (UG1)
```

Translation supplies every initial vertex.  Edges never leave a coset of
`m^(n-1)Z^3/m^nZ^3`, and each such coset is connected because the
unimodular set contains the three standard basis vectors.  Hence these cosets
are exactly the connected blocks, each identified with `Gamma_m`.

A vector is unimodular modulo `m` iff it is nonzero modulo every prime
dividing `m`.  This proves the CRT description and counts the degree by
inclusion-exclusion:

```text
deg(Gamma_m)=m^3 product_(p|m)(1-p^(-3)).
```

If `C` is a clique, reduction `C->F_p^3` is injective for every
`p|m`, so `|C|<=ell(m)^3`.  Conversely, label `ell(m)^3` points and,
for every `p|m`, inject that label set into `F_p^3`; choose compatible
lifts modulo `p^e` and combine them by CRT.  Distinct labels then differ
modulo every `p`, producing a clique of size `ell(m)^3`.

Before centralizing the marked commutator, the lamp kernel is the free
product of one involution for every site.  Centrality identifies every
orbital-edge commutator with the same central involution `w`.  Restricting
to one block therefore gives

```text
P_m=<w,(c_x)_(x in X_m) |
     w^2=c_x^2=1, w central, [c_x,c_y]=w for x~y>.       (UG2)
```

The affine--Clifford realization sends `w` to the nontrivial sign, so
`w!=1`.  Killing `w` in (UG2) gives exactly the RACG presentation,
and because `w` is central this proves

```text
1 -> <w> -> P_m -> W_(Gamma_m) -> 1.                    (UG3)
```

There are no edge relations between different connected blocks.  Grouping
the presentation by blocks makes the whole lamp kernel the free product of
the `P_m`'s with their copies of `<w>` amalgamated.  The vertical group
is transitive on blocks; the stabilizer of the base block is
`B_(m,1)=t^(-1)Bt`.  Its action on the block is the affine action on
`(Z/mZ)^3`.  The Bass--Serre tree of the central block amalgam now has
quotient one edge under `E_m`, with vertex and edge stabilizers exactly
those displayed in the claim.  This proves the general block normal form.
