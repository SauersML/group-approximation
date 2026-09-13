---
rg: 2
id: torsion-free-amenable-t-shape-adjunctions-are-aspherical
kind: claim
title: Adjoining one variable and one amenable-shape equation to a torsion-free group gives an aspherical 2-complex
distinct_from:
  klyachko-kl-holds-for-torsion-free: that is coefficient injectivity for exponent sum one; this adds the vanishing of the second homotopy group, so the cellular model is aspherical, and covers every amenable t-shape.
  aspherical-adjunction-has-zero-schur-kernel: that assumes asphericity and derives a zero Schur kernel; this supplies the asphericity for torsion-free coefficient groups.
artifacts:
  - research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md
---

Let `G` be torsion-free, `K` a `K(G,1)`-complex, and `w in G * <t>` cyclically
reduced. Put `L = (K v S^1_t) cup_w e^2`. Suppose the `t`-shape of `w` is
amenable in the sense of Fenn--Rourke. Then:

1. `G -> pi_1(L) = (G * <t>)/<<w>>` is injective;
2. `pi_2(L) = Z pi_1(L) (x)_(Z G) pi_2(K) = 0`;
3. `L` is aspherical, and the relative presentation `<G, t | w>` is aspherical
   in the Bogley--Pride sense.

**Amenable shapes.** The `t`-shape is the cyclic word of `t`-letters of `w`.
Its Magnus derivative deletes every subword `t t^-1` and closes up. The root
is the last shape before a pure power `t^q` is reached. A shape is amenable
when its root is `t t^-1` or a one-clump shape `t^p (t t^-1)^q`, `p, q > 0`, or
the inverse of one. Every shape of exponent sum `±1` is amenable. Amenable
shapes of exponent sum `±p` exist for every `p >= 1`, e.g. `t t t t^-1`, whose
root is itself. No proper-power shape is amenable.

Imported; see the citation route for exactly what was read.
