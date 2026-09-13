---
rg: 2
id: compiler-rope-edge-is-not-co-amenable-proof
kind: route
title: Embed the switch quotient in the core quotient, push the mean onto the Higman host, and assemble GKP 3.7 from product and separable factors
target: compiler-rope-edge-is-not-co-amenable
requires:
  - mf-safe-finite-presentation-compiler
  - mikhailova-coset-action-is-two-sided-q-action
  - centralizer-hnn-is-free-generalized-wreath
  - gkp-free-generalized-wreath-soficity
  - gkp-sofic-action-toolkit
  - separating-sofic-quotient-sets-make-an-action-sofic
---

Notation as in the target.

## (R1)

`F ∩ core_K(L) <= F ∩ L = N`. The composite `F -> K -> K/core_K(L)` has kernel
`F ∩ core_K(L)`, so `F/(F ∩ core_K(L))` embeds in `K/core_K(L)`. `F/N` is a
quotient of `F/(F ∩ core_K(L))`. Subgroups and quotients of amenable groups
are amenable. So if `K/core_K(L)` were amenable, `F/N` would be amenable,
which it is not. `∎`

## (R2)

`Q_e = B3(S_c)` is an HNN extension of `S_c * F(x,y)` (item 3), so it contains
the non-amenable group `F(x,y)`. Since `L_e ∩ F = N_e` and `F/N_e = Q_e`,
(R1) gives the first statement.

**Not co-amenable.** `K_e/L_e = (K_e^0/L_e^0) x (K^g/L^g)`, and `K_e` acts by
the product action. The projection onto the first factor is equivariant, and
`K^g` acts trivially on that factor. So an `K_e`-invariant mean on
`ell^infinity(K_e/L_e)` pushes forward to a `K_e^0`-invariant mean on
`ell^infinity(K_e^0/L_e^0)`. Since `L_e^0 = F x M_e`,

```text
K_e^0 / L_e^0  ~=  F(X_e)^2 / M_e  ~=  H_e,
```

and `F(X_e)^2` acts two-sidedly through `F(X_e) ->> H_e` ((TS) of
[[mikhailova-coset-action-is-two-sided-q-action]], applied to the finite
presentation of `H_e`). Restricting the mean to `F(X_e) x 1`, which acts by
left translation through a surjection, gives a left-invariant mean on `H_e`.
So `H_e` would be amenable. But the Higman embedding is injective (item 4),
so `H_e` contains `Q_e`, which contains `F(x,y)`. So no invariant mean
exists. `∎`

## (R3)

By [[centralizer-hnn-is-free-generalized-wreath]],
`Gamma_e ~= Z wr^*_(K_e/L_e) K_e`. `K_e` is a finite direct product of free
groups, so it is residually finite and sofic. By GKP Theorem 3.7
([[gkp-free-generalized-wreath-soficity]]) it suffices that
`K_e ↷ K_e/L_e` is sofic. By (S2) of
[[separating-sofic-quotient-sets-make-an-action-sofic]] it suffices that both
factors are sofic.

- **First factor.** `K_e^0 ↷ H_e` is the composition of the projection
  `K_e^0 = F x F(X_e)^2 ->> F(X_e)^2` with the two-sided action. That action is
  sofic by hypothesis, so the composition is sofic by GKP Proposition 2.15(1)
  ([[gkp-sofic-action-toolkit]]).
- **Second factor.** `L^g` is the graph of a homomorphism `iota : F -> P`
  into the residually finite group `P = F_2 x F_2`. Graphs of homomorphisms
  into residually finite groups are separable. If `p != iota(f)`, choose a
  finite quotient `r : P ->> C` with `r(p) != r(iota(f))`. Then
  `{ (f',p') : r(p') = r(iota(f')) }` is the preimage of the diagonal of
  `C x C`, so it has finite index. It contains `L^g` and avoids `(f,p)`. By
  (C1) of the same node, `K^g ↷ K^g/L^g` is sofic.

So `Gamma_e` is sofic. `∎`
