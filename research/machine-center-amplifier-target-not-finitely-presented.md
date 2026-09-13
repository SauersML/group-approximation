---
rg: 2
id: machine-center-amplifier-target-not-finitely-presented
kind: claim
title: The abstract target of the machine-center amplifier is never finitely presented
distinct_from:
  kazhdan-lamp-amplifier-for-machine-center: that asks for a finitely presented OVERGROUP K_e that merely contains the coset wreath on FIN; this proves the abstract target group itself (attempt A3's realization G_e x (Phi_e wr G/Gamma)) is not finitely presented, so any solution must be a strictly larger container.
  compression-wreath-not-finitely-presented: that proves K^(G*/Gamma*) x| G* is not finitely presented for the multi-mover HNN compression pair with a height homomorphism; this is the Kun--Thom Theorem E pair and the switchable machine center Phi_e, and it makes the obstruction unconditional by quoting the general infranormal-non-normal double-coset theorem rather than a height map.
---

ESTABLISHED.  Let `Gamma <= G` be the Kun--Thom Theorem E infranormal
non-normal Kazhdan pair ([[kun-thom-nonsofic-wreath]]), let `G_e = G(P(M_e))`
be the pumped clocked machine group, and let `Phi_e <= Z(G_e)` be its
switchable center ([[machine-center-vanishes-exactly-on-inf]]).  For every
`e in FIN` the abstract target of the amplifier
([[kazhdan-lamp-amplifier-for-machine-center]], attempt A3),

```text
T_e  =  G_e x ( Phi_e wr_(G/Gamma) G )       (Phi_e != 1 on FIN),
```

is **not finitely presented**, and neither is the coset wreath
`Phi_e wr_(G/Gamma) G` itself.

The obstruction is unconditional and does not depend on any special feature of
the Theorem E pair: it holds for **every** infranormal non-normal pair,
because every such pair has infinitely many double cosets
([[strict-one-sided-compression-forces-infinite-bi-index]], SCI5).  So the
attempt-A3 realization can never be repaired by attack (a) — hunting for an
infranormal non-normal Kazhdan pair with `|Gamma \ G / Gamma| < infinity` — as
no such pair exists.

## What this does and does not settle

- It closes attempt A3 of [[kazhdan-lamp-amplifier-for-machine-center]]
  unconditionally: the group A3 actually builds is not finitely presented.
- It does **not** refute the amplifier.  The amplifier only asks for a
  finitely presented `K_e` that *contains* the coset wreath on FIN.  Since the
  wreath is finitely generated (`G` together with one root copy of `Phi_e`,
  because `G` acts transitively on `G/Gamma`) and recursively presented
  uniformly in `e`, a finitely presented container exists abstractly by Higman
  embedding.  What is open is soficity of such a container on INF, which is the
  content of [[machine-center-amplifier-is-a-sofic-safe-compiler-instance]].

DERIVATION [[machine-center-amplifier-target-not-fp-proof]].
