---
rg: 2
id: binary-affine-safe-perfect-support-forces-classical-satisfaction
kind: claim
title: Binary affine-safe perfect edge supports force a perfect classical strategy
distinct_from:
  tailored-gap-is-lcs-or-has-a-nonaffine-edge: that classifies full accepted relations in arbitrary answer alphabets; this uses the positive support of one perfect strategy and closes the binary-answer case even when the ambient relation is nonaffine.
  functional-support-is-affine-exactly-on-an-affine-domain-map: that classifies functional graphs abstractly; this proves the stronger global classical-collapse theorem for arbitrary binary relations.
  perfect-commuting-unique-game-is-classically-satisfiable: that transports labels through bijective constraints in arbitrary alphabets; this allows arbitrary binary relations and needs only affine safety of the positive edge supports.
---

**ESTABLISHED BINARY SUPPORT COLLAPSE.**  Let `G` be a finite two-player
game in which both answer alphabets are `F_2`.  Fix a perfect commuting
strategy and, for every asked edge `e=(x,y)`, let

```text
S_e = {(a,b): ||P_x^a Q_y^b xi|| > 0}
```

be its positive correlation support.  If

```text
Aff_F2(S_e) subseteq R_e                              (BAS1)
```

for every accepted relation `R_e`, then `G` has a perfect deterministic
classical strategy.  Hence no binary-answer game with perfect commuting value
one and finite-dimensional value below one can have affine-safe positive
support on every edge.

The Boolean square has an exact minimal classification.  Every subset of
`F_2^2` of size zero, one, two, or four is affine; a three-point subset has
affine hull all of `F_2^2`.  It follows that any binary perfect
commuting-versus-finite gap must contain an edge for which

```text
R_e = S_e = F_2^2 minus {g}                           (BAS2)
```

for one rejected pair `g`: all three accepted pairs must occur positively.
Up to independent input/output bit flips this is the unique minimal nonlinear
binary fiber.

In particular every **partial binary projection constraint** is harmless.
Its accepted relation is the graph of a partial function
`f:D->F_2`, where `D subseteq F_2`; it has at most two points and is affine.
Thus a binary partial-projection game with a perfect commuting strategy always
has a perfect classical strategy.  Non-uniqueness can evade the earlier
unique-game collapse only by introducing the full three-of-four fiber `(BAS2)`;
there is no affine-safe binary projection or relational bypass.
