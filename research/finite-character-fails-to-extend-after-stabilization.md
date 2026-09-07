---
rg: 2
id: finite-character-fails-to-extend-after-stabilization
kind: claim
title: A finite character of the units of a countable simple stably finite ring can fail to extend to rank two
distinct_from:
  mf-representations-of-units-extend-under-stabilization: that is the positive extension theorem for purely infinite simple rings; this is the counterexample in the simple stably finite case, with a finite target, so the two together locate the phenomenon in pure infiniteness.
  unit-abelianization-to-algebraic-k1-not-injective: that is the failure of injectivity into algebraic K_1 for the C-star algebra; this converts the same witness into a representation-extension failure over a countable simple ring, with a character onto a finite group.
  simple-ah-witness-is-elementary-in-rank-two: that is the elementary factorization; this is the group-theoretic consequence of it for characters.
artifacts:
  - research/artifacts/k1-classification-and-extension-bridge-2026-09-07.md
---

There are a countable unital simple stably finite ring `S` and a surjective
character

```text
chi : S^x --> C_2
```

which does not extend along `iota_2 : S^x -> GL_2(S)`: no homomorphism
`GL_2(S) -> C_2` restricts to `chi`.

`S` is a countable `Q`-subalgebra of the AH algebra of
`stw59-simple-ah-non-k1-injective`, and the same construction with the
factorial family gives any prescribed nontrivial finite cyclic target.

The obstruction is visible to a finite, hence MF, target group.
