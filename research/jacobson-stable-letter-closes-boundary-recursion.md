---
rg: 2
id: jacobson-stable-letter-closes-boundary-recursion
kind: claim
title: Seven stable-letter relations close the full Jacobson boundary recursion and retain the head
distinct_from:
  jacobson-full-boundary-forces-six-coordinate-packet: that reconstructs one larger finite packet in Theta; this adds an explicit stable letter and proves every shifted boundary packet in a new finitely presented candidate.
  jacobson-recursive-affine-cells-do-not-force-boundary: that supplies a finite countermodel to a selected subset of the old recursive equations; this supplies new conjugation relations which enforce the entire boundary packet at every shift.
artifacts:
  - research/artifacts/jacobson-stable-letter-recursion-and-matrix-gap-2026-09-08.md
---

Use the exact finite factors and their specified embeddings

```text
B=GL_6(F_2) x delta(GL_3(F_2)),
C=C_0 x C_far ~= GL_5(F_2) x GL_3(F_2),
Z=B intersect C=C_0 x delta(K_P).
```

Inside `B`, the original head is `g_Q`, the first local tail is
`tau(g)`, and the original tail is `g_P=tau(g)delta(g)`.
Inside `C`, `h=(h_0,w_12)` and `h_1=(1,w_12)=h_0 h`.
Let `Sigma={x_13,x_31,w_23}`, a generating set of `GL_3(F_2)`.

Define `Theta_shift` by the existing full-boundary presentation
`Theta` and a new generator `t` with seven additional relations:

```text
t g_Q t^-1=tau(g)            for g in Sigma,
t g_P t^-1=delta(g)          for g in Sigma,
t h t^-1=h_1.
```

This is an explicit finitely presented group. Its head involution
`w=x_13,Q` is nontrivial, and both finite packets retain their
faithful literal images. The group also surjects onto the additive
group of integers by the exponent of `t`.

Conjugation by `t` transports the entire original finite boundary
packet, including

```text
[u_1,h_1 tau(x_23) h_1]=tau(x_23),
u_1=[h_1 delta(x_13) h_1,delta(x_31)].
```

All finite-packet and mixed relations recur under every iterate of
this same conjugation. Nontriviality is witnessed by extending the
literal half-line action by the identity at negative levels and
letting `t` translate the resulting bilateral basis.

The new relations are additional presentation data. No assertion
that all of `Theta` embeds in `Theta_shift`, or that the new group
is non-MF, follows from this recursion theorem alone.

DERIVATION
jacobson-bilateral-stable-letter-proof
