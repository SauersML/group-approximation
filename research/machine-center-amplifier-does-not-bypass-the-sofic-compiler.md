---
rg: 2
id: machine-center-amplifier-does-not-bypass-the-sofic-compiler
kind: claim
title: The machine-center amplifier is a sofic-safe compiler instance and is dominated by the compiler with a finitely presented seed
distinct_from:
  kazhdan-lamp-amplifier-for-machine-center: that is the open construction problem; this places it in the reduction order, showing any solution to it is a sofic-safe compilation with a nonsofic seed and so cannot avoid the compiler's positive branch.
  sofic-safe-finite-presentation-compiler: that is the compiler with its own Mikhailova-rope positive branch; this shows the amplifier solves the same second-level goal only by solving a compiler whose seed is not even finitely presented, so the compiler with the eighteen-relator seed dominates the amplifier.
---

ESTABLISHED (unreviewed).  The machine-center amplifier
([[kazhdan-lamp-amplifier-for-machine-center]]) does not give a route to
[[sofic-recognition-finite-presentations-is-pi2-complete]] that avoids the
positive branch of [[sofic-safe-finite-presentation-compiler]].  Precisely:

1. **The seed it would introduce is nonsofic but not finitely presented.**
   On FIN the amplifier's output contains the fixed group
   `E' = (Z/2) wr_(G/Gamma) G` (`Gamma <= G` the fixed Theorem E pair,
   independent of `e`).  `E'` is nonsofic (Theorem A,
   [[kun-thom-nonsofic-wreath]]) and is **not finitely presented**
   ([[machine-center-amplifier-target-not-finitely-presented]]).

2. **Any amplifier solution is a sofic-safe compilation.**  A solution is a
   total computable `e |-> K_e` into finite-presentation codes with `K_e` sofic
   on INF and `E' ↪ K_e` on FIN (soficity passes to subgroups, so containing
   `Phi_e wr_(G/Gamma) G` forces containing `E'`).  That is by definition a
   sofic-safe finite-presentation compilation with the nonsofic seed `E'`.  By
   (1) and [[machine-center-amplifier-target-not-finitely-presented]], `K_e`
   cannot be the wreath itself nor retract onto `E'`; it must contain `E'` as a
   proper subgroup, i.e. be a genuine Higman-type container, whose soficity on
   INF is exactly the positive branch the compiler node isolates.

3. **Domination by the finitely presented seed.**  A fixed *finitely presented*
   nonsofic group now exists ([[explicit-eighteen-relator-nonsofic-group]]).
   The sofic-safe compiler run with that seed proves SOFIC_fp complete using
   the same positive branch and a strictly simpler, finitely presented, seed.
   The amplifier therefore offers no reduction not already offered by the
   compiler, and its seed is worse (not finitely presented).

## Strategic consequence

The open crux for `SOFIC_fp` `Pi^0_2`-completeness is the compiler's positive
branch — soficity of the centralizing HNN / Higman rope over a non-amenable,
non-separable edge (`sofic-safe-finite-presentation-compiler`, and the special
case `<B, t | [t, S] = 1>` with `S <= B` non-amenable and `B` sofic) — not the
machine-center amplifier.  The machine center's genuine dividend is upstream and
already banked: the switchable center `Phi_e`
([[machine-center-vanishes-exactly-on-inf]]) and the unconditional death of the
emergent-lamp route via infinite double cosets
([[machine-center-amplifier-target-not-finitely-presented]]).

DERIVATION [[amplifier-compiler-domination-proof]].
