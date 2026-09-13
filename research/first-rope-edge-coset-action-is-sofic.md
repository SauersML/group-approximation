---
rg: 2
id: first-rope-edge-coset-action-is-sofic
kind: claim
title: On INF the compiler's first rope acts soficly on the cosets of its twisted edge S_e
distinct_from:
  product-of-free-groups-set-actions-are-sofic: that concerns actions of F x F', which feed soficity of the first rope as a group; this is one action of the first rope itself, on the cosets of S_e.
  compiler-rope-edge-is-not-co-amenable: its (R3) isolates the two-sided Higman-host action that makes Gamma_e sofic; this is the action that carries the second rope.
  twisted-rope-envelope-coset-action-is-sofic: that is the envelope action, which this implies by the landed reduction.
---

OPEN. Take the compiler of [[mf-safe-finite-presentation-compiler]] and
`e in INF`, with the first rope `Gamma_e = < K_e, v | [v, L_e] = 1 >` and the
edge `S_e = <F, vFv^-1> = F *_(N_e) F^v`. The claim is that the coset action
`Gamma_e action Gamma_e/S_e` is sofic (GKP Definition 2.1(5)).

**What it gives.** Together with soficity of `Gamma_e`:

- the twisted rope `R_e` is sofic, via
  [[envelope-coset-action-sofic-once-edge-coset-action-sofic]] and
  [[twisted-rope-is-a-central-rope-over-an-rf-envelope]];
- the untwisted rope `< Gamma_e, z | [z,S_e] = 1 >` is sofic, via GKP
  Theorem 3.7.

## Attempts

- **Structure of the edge (verified).** By
  [[centralizer-hnn-is-free-generalized-wreath]],
  `Gamma_e = F(X) x| K_e` with `X = K_e/L_e` and `v = z_(x_0)`. Since
  `f z_(x_0)^-1 f^-1 = z_(f x_0)^-1`,
  - `S_e = A_Y x| F`, where `Y = F.x_0 ~= F/N_e`;
  - `A_Y = < z_y z_(y')^-1 : y, y' in Y >` is a free factor of `F(Y)` with
    complement `<z_(x_0)>`.
  The space `Gamma_e/S_e` fibres equivariantly over `K_e/F`, and the fibre
  over `kF` is `F(X)/A_(kY)`. In the Schreier graph of that fibre, every
  point `z_y^-1 A_(kY)`, `y in kY`, is the same point, so the base coset is a
  hub. Everything else is free.
- **Base and fibres separately (both sofic).** `F` sits in `K_e` as the graph
  of a homomorphism over the first free factor. It is closed in the
  residually finite group `K_e`, so `K_e action K_e/F` is sofic by (C1) of
  [[separating-sofic-quotient-sets-make-an-action-sofic]]. Every action of a
  free group is sofic (GKP Theorem 2.19), so each fibre action is sofic.
- **The gluing (dies for lack of a theorem).** No recorded result combines
  them. What is needed is a set-action analogue of GKP Theorem 3.7 for
  `F(X) x| K_e` acting on the induced family `F(X)/A_(kY)`. Lamp models are
  indexed by a model of `K_e action X`, and hubs are indexed by a model of the
  incidence set `K_e/N_e <= K_e/F x K_e/L_e`. The hub relations
  `sigma_y^-1(b) = sigma_(y')^-1(b)` couple the lamp permutations. Independent
  random lamps do not satisfy them.
- **Separation by larger subgroups (not enough).** The maps from
  `Gamma_e/S_e` onto `K_e/F`, and onto the coset space of the abelian-lamp
  image `(sum_Y Z)_0 x| F` in `Z wr_X K_e`, lose the non-abelian fibre
  information.
