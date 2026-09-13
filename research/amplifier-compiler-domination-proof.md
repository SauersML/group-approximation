---
rg: 2
id: amplifier-compiler-domination-proof
kind: route
title: An amplifier solution is a sofic-safe compilation with seed E', which the finitely presented seed dominates
target: machine-center-amplifier-does-not-bypass-the-sofic-compiler
requires:
  - machine-center-amplifier-target-not-finitely-presented
  - kun-thom-nonsofic-wreath
  - explicit-eighteen-relator-nonsofic-group
---

The pair `Gamma <= G` (Theorem E, [[kun-thom-nonsofic-wreath]]) is fixed once
and for all; only `Phi_e` depends on `e`.  Put `E' = (Z/2) wr_(G/Gamma) G`, a
fixed group.

## Step 1: E' is a fixed nonsofic non-finitely-presented seed

Nonsoficity is Theorem A of [[kun-thom-nonsofic-wreath]].  Non-finite-
presentation is [[machine-center-amplifier-target-not-finitely-presented]]:
its retract-closure argument gives that `(Z/2) wr_(G/Gamma) G` is not finitely
presented, from Cornulier's wreath criterion and infinite double cosets.

## Step 2: amplifier solution => sofic-safe compilation with seed E'

Suppose `e |-> K_e` solves [[kazhdan-lamp-amplifier-for-machine-center]]: `K_e`
is finitely presented and computable in `e`, sofic for `e in INF`, and contains
`Phi_e wr_(G/Gamma) G` for `e in FIN`.  On FIN, `Phi_e != 1`
([[machine-center-vanishes-exactly-on-inf]], via the previous node), so
`E' <= Phi_e wr_(G/Gamma) G <= K_e`.  Soficity passes to subgroups, so `K_e`
nonsofic on FIN.  Thus `e |-> K_e` is a total computable map into finite-
presentation codes with

```text
e in INF  =>  K_e sofic,
e in FIN  =>  the fixed nonsofic E' embeds in K_e,
```

which is precisely a sofic-safe finite-presentation compilation
([[sofic-safe-finite-presentation-compiler]]) with seed `E'`.  By Step 1 and
[[machine-center-amplifier-target-not-finitely-presented]], `K_e` is not the
wreath and does not retract onto `E'`, so it contains `E'` as a proper
subgroup: a genuine Higman-type container.  Its INF soficity is the compiler's
positive branch.  Hence any amplifier solution yields a compiler solution;
the amplifier is at least as hard as the compiler.

## Step 3: the finitely presented seed dominates

A sofic-safe compiler is not tied to any one seed: its negative branch embeds
whatever fixed nonsofic group is chosen, and its positive branch (soficity of
the container on INF) does not depend on the seed.  A fixed *finitely
presented* nonsofic seed exists, [[explicit-eighteen-relator-nonsofic-group]].
Running the compiler with that seed proves
[[sofic-recognition-finite-presentations-is-pi2-complete]] using the same
positive branch and a finitely presented seed, whereas the amplifier is forced
to use the non-finitely-presented seed `E'`.  So the amplifier offers no
reduction the compiler does not already offer, with a strictly worse seed.

## What is NOT claimed

This does not solve the compiler and does not refute the amplifier.  It orders
the two problems: `amplifier => compiler(E') => SOFIC_fp complete`, and
`compiler(eighteen-relator) => SOFIC_fp complete` with a simpler seed.  The
converse `compiler => amplifier` is not claimed and is not needed: once the
compiler is solved the amplifier is moot.
