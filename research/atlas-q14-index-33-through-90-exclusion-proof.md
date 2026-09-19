---
rg: 2
id: atlas-q14-index-33-through-90-exclusion-proof
kind: route
title: Combine the unique Sp6(2) interval carrier with the natural A10 collapse
target: atlas-q14-simple-overgroup-index-is-at-least-91
requires:
  - atlas-q14-simple-overgroup-index-is-at-least-33
  - atlas-a8-index-33-to-89-is-orthogonal-sp6
  - atlas-a4-sp6-packet-collision-screen
  - atlas-natural-a8-supports-collapse-before-collision
---

Write `n=[S:A]`.  The established lower bound gives `n>=33`.  If `n<90`,
the finite-simple overgroup classification gives

```text
S ~= Sp_6(2),   n=72,
```

and puts both chart subgroups in the single orthogonal `A8` conjugacy class.
The exact `Sp_6(2)` screen ranges the relative conjugator over the whole
ambient group and includes both label parities through the `S8` normalizer.
It finds no pair satisfying the packet and `q_19243`, contradicting the
marked system.  Hence `n>=90`.

If `n=90`, then `|S|=1814400`; the same complete simple-order table identifies
`S ~= A10`.  Restrict the natural degree-ten permutation action to either
embedded `A8`.  Its only nontrivial transitive orbit degree below fifteen is
eight.  Faithfulness therefore forces orbit shape

```text
8+1+1,
```

so each chart is a natural support `A8`.  The established natural-support
theorem says the packet forces their eight-point supports to coincide, after
which `q_19243` excludes every relative automorphism alignment.  This is the
final contradiction, so `n>=91`.

