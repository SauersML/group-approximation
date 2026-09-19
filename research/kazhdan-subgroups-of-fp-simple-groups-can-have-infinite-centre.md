---
rg: 2
id: kazhdan-subgroups-of-fp-simple-groups-can-have-infinite-centre
kind: claim
title: The integral Jacobi group Sp_2n(Z) ⋉ H(Z), n ≥ 2, is an integral linear Kazhdan group with infinite cyclic centre, so "Kazhdan subgroups have finite centre" does not separate Boone–Higman
distinct_from:
  central-kazhdan-residual-separator-for-boone-higman: that is the live separator, about central elements that die in every finite quotient; this kills only the naive form "finite centre", whose witness here is residually finite.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that is a Kazhdan group with infinite centre that is not residually finite and not linear; this is an integral linear one, so it sits in a known finitely presented simple group.
  kazhdan-subgroups-of-brin-thompson-groups-have-finite-center: that is the open finite-centre question for nV hosts; this shows the finite-centre condition fails in some other finitely presented simple group, so it cannot be a property of all of them.
---

**ESTABLISHED** (lane proof, elementary; the Kazhdan property of the real Jacobi group is recalled, not re-read at source; no priority claimed).

## Statement

Let `n >= 2` and let `ω` be the standard symplectic form on `Z^(2n)`, with Gram matrix `J`.
- **The group.** `H_Z = Z^(2n) × Z` with `(v,t)(v',t') = (v+v', t+t'+ω(v,v'))`. `Sp_2n(Z)` acts by `g·(v,t) = (gv, t)`; this is an automorphism because `ω(gv,gv') = ω(v,v')`. Put `Γ_n = Sp_2n(Z) ⋉ H_Z`.
- **Properties.** `Γ_n` is finitely generated, has property (T), is a subgroup of `GL_(2n+2)(Z)`, and has infinite cyclic centre `{(1,(0,t))}`.
- **Consequence.** `Γ_n` lies in a finitely presented simple group. So the subgroup-closed class `P_fc` of groups all of whose finitely generated Kazhdan subgroups have finite centre does not contain every finitely presented simple group. It fails (S1) of `hereditary-approximation-disproofs-of-boone-higman`, and so cannot separate Boone–Higman.

## Proof

1. **Integral linearity.** Send `(v,t)` to the `(2n+2)×(2n+2)` matrix `M(v,t)` with block rows `[1, v^T J, t]`, `[0, I, v]`, `[0, 0, 1]`.
   - Block multiplication gives `M(v,t)M(v',t') = M(v+v', t+t'+v^T J v')`, and `v^T J v' = ω(v,v')`. So `M` is an injective homomorphism of `H_Z`.
   - For `g ∈ Sp_2n(Z)` put `D(g) = diag(1, g, 1)`. Then `D(g) M(v,t) D(g)^(-1)` has blocks `[1, v^T J g^(-1), t]`, `[0, I, gv]`, `[0, 0, 1]`. Since `g^T J g = J` gives `v^T J g^(-1) = (gv)^T J`, this is `M(gv, t)`.
   - So `(g,(v,t)) ↦ D(g)M(v,t)` is a homomorphism `Γ_n → GL_(2n+2)(Z)`. It is injective: the middle diagonal block recovers `g`, and `M` is injective.
2. **Centre.** `(1,(0,t))` commutes with `H_Z`, because `ω(0,·) = 0`, and with `Sp_2n(Z)`, which fixes `t`. So the centre contains `{(1,(0,t)) : t ∈ Z} ≅ Z`. Conversely, a central `(g,(v,t))` commutes with every `(1,(w,0))`, which forces `g = 1` and `ω(v,·) = 0`, so `v = 0`. Hence the centre is exactly `Z`.
3. **Property (T).** `Γ_n` is a lattice in the real Jacobi group `G = Sp_2n(R) ⋉ H(R)`, which has (T) for `n >= 2`. This is recalled from S. P. Wang's criterion for connected Lie groups: the Levi factor `Sp_2n(R)` has (T), and it fixes no nonzero vector of the abelianized radical `H(R)/[H(R),H(R)] = R^(2n)`. The criterion is not re-read here. Property (T) passes to lattices.
4. **Hosts.** `Γ_n ≤ GL_(2n+2)(Z)` lies in the one finitely presented simple group of `one-fp-simple-group-contains-every-integral-linear-group`, which bh-verify-W passed. It also has its own host by `finitely-generated-linear-groups-satisfy-boone-higman`.

## What survives

`Γ_n` is residually finite, being integral linear. So its central elements are all detected by finite quotients. The live form of the "central Kazhdan wall" is the residual one, `central-kazhdan-residual-separator-for-boone-higman`: central elements of Kazhdan subgroups that die in every finite quotient.

## Lesson for general BH

An infinite centre in a Kazhdan subgroup is no obstruction for finitely presented simple groups. What distinguishes the hard inputs (Deligne's lattice, Nowak's Q_{g,c}, St_N(R_L)) is that their centres are invisible to finite quotients, not that they are large.
