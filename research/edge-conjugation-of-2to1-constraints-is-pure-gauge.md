---
rg: 2
id: edge-conjugation-of-2to1-constraints-is-pure-gauge
kind: claim
title: Relabelling the left alphabet of a 2-to-1 constraint leaves the folded long-code restriction literally unchanged
invalidates:
  - rich-2to1-via-edge-conjugation-randomization
artifacts:
  - research/artifacts/unique-games-affine-orientation-2026-08-24.md
---

**ESTABLISHED.**  Let `pi : A -> B` be a 2-to-1 map, let `sigma` be a
permutation of the left alphabet `A`, and set

```text
pi^sigma = pi . sigma^{-1}.
```

Write `P_pi : {-1,1}^B -> {-1,1}^A` for the pullback `(P_pi y)_a = y_{pi(a)}`,
so that the folded restriction of a long-code function `F` is
`F|_pi = F . P_pi`, a function on `{-1,1}^B`.  Let `sigma` act on
assignments by `(sigma . X)_a = X_{sigma^{-1}(a)}`.  Preserving dictator
completeness under the relabelling forces the long code to transform as

```text
F^sigma(X) = F(sigma^{-1} . X).
```

Then, for every `y in {-1,1}^B`,

```text
(F^sigma)|_{pi^sigma}(y) = F|_pi(y).                                    (G1)
```

The computation is one line: `(sigma^{-1} . Z)_a = Z_{sigma(a)}`, and with
`Z = P_{pi . sigma^{-1}} y` this is `y_{pi(sigma^{-1}(sigma(a)))} = y_{pi(a)}`,
so `sigma^{-1} . Z = P_pi y`.

**Consequence.**  Conjugating a constraint is pure gauge for the analytic
object a dictatorship test reads: every bit of the apparent new randomness
cancels out of `F|_pi`.  So richness cannot be manufactured by randomizing
the constraints of an already-hard 2-to-1 instance edge by edge -- the test
sees the instance it started with.

**Scope, stated so it is not overread.**  `(G1)` is a per-edge identity.
It shows that no per-edge functional of the folded restriction changes.  It
does *not* prove that every global randomization scheme is useless: the
joint law of which vertices receive which `sigma`, and hence any statistic
correlating two different edges at a shared vertex, is untouched by this
computation.  What is closed is the local move, which is the one that looks
free.

The proof is `edge-conjugation-2to1-gauge-identity-proof`.
