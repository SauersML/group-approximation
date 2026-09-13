---
rg: 2
id: perfect-group-relator-width-over-nilpotent-groups
kind: claim
title: A finitely generated perfect group has uniformly bounded relator width over every nilpotent group, so it has no weak models in nilpotent groups
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that bounds relator width over symmetric, alternating, sporadic and bounded-rank Lie type groups, using simplicity and nonsoficity; this bounds it over nilpotent groups of every class using only perfection, by a Lie-ring correction argument.
  howie-pro-p-tuple-fails-the-profinite-certificate-at-a5: that shows Howie's pro-p width-two phenomenon carries no profinite information; this explains it from the other side, since bounded pro-nilpotent width holds for every perfect presentation.
  glebsky-rivera-w-sofic-criterion: that characterizes weak soficity through all finite quotients of the free group; this shows the nilpotent quotients never contribute unbounded width for a perfect group.
---

**ESTABLISHED.** Let `F` be free on a finite set `X`, and `R ⊂ F` a finite set whose exponent-sum
vectors `e_r` span `Z^X`. This holds for a finite subset of the relators of any finitely generated
perfect group `G = F/<<R'>>`. For `x in F` choose integers `n_r` with `e_x = sum_r n_r e_r`, and put

```text
K(x) = sum_r |n_r| + 2 |R| .
```

Then for every `k >= 1`, `x` is a product of `K(x)` conjugates of elements of `R^(+-1)` modulo
`gamma_(k+1)(F)`, with one fixed sign-and-relator pattern for all `k`. Consequently:

1. For every nilpotent group `Q` and every `a in Q^X`, `x(a)` is a product of at most `K(x)`
   `Q`-conjugates of relator values `r(a)^(+-1)`.
2. For every bi-invariant pseudo-length `l` on a nilpotent group,
   `l(x(a)) <= K(x) max_(r in R) l(r(a))`.
3. A nontrivial finitely generated perfect group admits no weak models in nilpotent groups with any
   bi-invariant lengths. So a group containing one is not approximable by nilpotent groups: finite
   `p`-groups of unbounded class, free nilpotent quotients, and unitriangular groups all fail.

**Mechanism.** Degree one of the lower central series is matched by the exponent sums. At degree
`j`, the defect lies in `L_j = gamma_j/gamma_(j+1)`, the degree-`j` part of the free Lie ring. It
equals `[L_1, L_(j-1)] = sum_r [e_r, L_(j-1)]`, because the `e_r` span `L_1`. It is removed by
conjugating the second member of a fixed pair `r, r^-1` by an element of `gamma_(j-1)(F)`. The
corrections at different degrees reuse the same `2|R|` factors.

**For the weak-soficity lane.** An earlier attempt node
(`non-linear-sofic-simple-groups-bounded-width-in-classical-groups`) listed `p`-groups of growing
class as possible room for weak models of the binary Leavitt unit group. That is excluded: `R^x`
is perfect. The remaining room consists of finite groups that are neither nilpotent nor of the
symmetric, alternating, sporadic or bounded-rank types, and classical groups under the open
covering step. Solvable groups of bounded derived length are expected to reduce the same way
(for the metabelian layer through `Lambda^2` of the exponent lattice), but this is not written.

**Credit.** Elementary (Magnus--Witt and free Lie rings). The graph check found no prior node;
no literature search was run.

Derivation: `perfect-group-relator-width-over-nilpotent-groups-proof`.
