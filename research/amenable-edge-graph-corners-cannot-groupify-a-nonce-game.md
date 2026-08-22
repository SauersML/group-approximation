---
rg: 2
id: amenable-edge-graph-corners-cannot-groupify-a-nonce-game
kind: claim
title: Amenable-edge graphs of hyperlinear groups cannot host a no-CE game corner
distinct_from:
  common-corner-literal-contexts-stop-at-bass-serre: that excludes finite graphs of finite groups by virtual freeness; this permits arbitrary hyperlinear vertex groups and arbitrary amenable edge groups.
  amenable-edge-hnn-preserves-hyperlinearity: that treats one HNN extension; this closes an arbitrary finite graph of groups under both amalgamated-product and HNN steps and applies the result to every algebraic game-corner map.
  finite-support-corner-localizes-obstruction: that says the finite support of a successful corner already generates a nonhyperlinear subgroup; this proves that no such subgroup can first arise from amenable-edge Bass--Serre assembly of hyperlinear pieces.
---

**ESTABLISHED.**  Let `Gcal` be a finite connected graph of countable groups.
Assume every vertex group `G_v` is hyperlinear and every edge group `G_e` is
amenable (with injective edge maps).  Then its Bass--Serre fundamental group

```text
Pi=pi_1(Gcal)                                             (AEG1)
```

is hyperlinear.

Consequently, let `B` be a rational game/BCS star algebra having tracial
states but no Connes-embeddable tracial state.  There are no

```text
0!=q=q^*=q^2 in Q[Pi],
Phi:B -> q Q[Pi] q,                 Phi(1)=q.             (AEG2)
```

Indeed, the normalized canonical trace of the hyperlinear group `Pi`, pulled
back through `Phi`, would be a Connes-embeddable tracial state of `B`.

This rules out a broader proposed construction than finite packet
amalgamation.  One may enlarge every local packet vertex by a free, amenable,
residually finite, arithmetic-hyperlinear, or otherwise known hyperlinear
auxiliary group; if all compatibility interfaces remain amenable and the
assembly is a graph of groups, it still cannot be the first source of the
required corner.  A successful Bass--Serre construction must use a
nonamenable edge at the load-bearing step and prove a genuinely new failure
of hyperlinearity there, or else leave graph-of-groups syntax.

The conclusion does not say that every nonamenable-edge graph is
nonhyperlinear.  It only identifies amenability of every edge as a complete
permanence fence.

