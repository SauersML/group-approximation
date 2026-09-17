---
rg: 2
id: relation-cover-sofic-envelope-forces-trivial-kernel
kind: claim
title: In the Kazhdan relation-cover reduction the induced-module envelope forces the abelian kernel to vanish, so the reduction adds no new torsion-free sofic quotientless Kazhdan groups
distinct_from:
  kazhdan-rational-relation-cover-reduction: that proves the reduction and its item-4 soficity criterion; this shows the criterion is only ever met when the abelian kernel A is zero and K is Q itself.
  kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion: that is the general statement about Kazhdan subgroups of lamp wreath products; this applies it to the relation-cover envelope and adds the saturation lemma for Rips covers.
  relation-cover-rational-lifting-over-quotientless-kazhdan: that is the open existence statement with clauses (RLT) and the induced envelope; this proves that statement is equivalent to the bare existence of a torsion-free sofic quotientless Kazhdan group, and false for every Q with torsion.
  titz-witzel-kernel-sofic: that asks soficity of one specific torsion-free simple Kazhdan lattice; this says nothing about any specific group and only removes the relation-cover machine as a source of soficity.
artifacts:
  - research/relation-cover-sofic-envelope-forces-trivial-kernel-proof.md
  - research/kazhdan-subgroups-of-lamp-wreaths-meet-base-in-torsion.md
  - research/kazhdan-rational-relation-cover-reduction.md
---

**ESTABLISHED.** The notation is that of `kazhdan-rational-relation-cover-reduction`,
`(RC1)`:

- `Q` is a nontrivial Kazhdan group with no nontrivial finite quotient;
- `pi: P ->> Q` is a surjection from a finitely generated Kazhdan group, with
  kernel `R`;
- `R_sat` is the preimage of `tors(R^ab)`, `K = P/R_sat`, `A = R/R_sat`, and
  `V = QQ (x)_{ZP} I_P`.

**1. The envelope kills the kernel.** Suppose `V` embeds `QQ[Q]`-equivariantly
into a permutation module `(+)_{x in X} W`, for some countable abelian `W` and
countable `Q`-set `X`. This includes clause 2 of
`relation-cover-rational-lifting-over-quotientless-kazhdan`, where `X = Q`. Then

```text
A = 0,    R^ab is torsion,    R = R_sat,    K = Q.                  (EK0)
```

**2. Incompatibility with (RLT).** Under the hypothesis of item 1, (RLT) holds
if and only if `Q` is torsion-free. In particular, if `Q` has an element of
prime order, no Kazhdan cover satisfies both clauses. This covers the
suggested `Q = EL_3(LC(X,F_q) semidirect Z)`, which contains elementary
matrices of order `p`.

**3. The open lifting claim is the bare kernel problem.** The following are
equivalent:

- (a) `relation-cover-rational-lifting-over-quotientless-kazhdan` holds;
- (b) there is a nontrivial torsion-free, sofic, Kazhdan group with no nontrivial
  finite quotient.

For (b) => (a), take `P = Q`. So the relation-cover machine, in its only
soficity mechanism, produces nothing beyond its input.

**4. Saturation lemma.** Let `N <= R` be normal in `P` with `N^ab` torsion, for
example `N` Kazhdan or a quotient of a Kazhdan group. Then:

- `N <= R_sat`;
- the reduction for `pi` and the reduction for `pi-bar: P/N ->> Q` have the same
  `R_sat/N`, the same `K` and the same `A`;
- (RLT) holds for `pi` if and only if it holds for `pi-bar`.

**5. Consequence for hyperbolic Rips covers.** In Attempt 4 of the lifting
claim, `G ->> Q' ->> Q` comes from `belegradek-osin-rips-construction`. The
kernel `N` of `G ->> Q'` is a quotient of the Kazhdan group `H`, so `N^ab` is
finite. By item 4, (RLT) and `K` for `G` coincide with (RLT) and `K` for
`Q' ->> Q`. The absence of root elements in the hyperbolic group `G` is
illusory: every question is decided in `Q'`.

**The invariant and the step where every member dies.** The item-4 embedding
`K -> V semidirect Q` of the reduction sends `A` into the lamp group. A Kazhdan
subgroup of a lamp wreath product meets the lamps only in torsion. That follows
from the shrinking product Haar measures on the dual lamp group, where an
invariant vector must live on a null annihilator. `A` is torsion-free, so it
dies. Any soficity argument for `K` with `A != 0` therefore has to leave the
class of permutation-module envelopes, and in particular must not place `A` in
the base of any lamp wreath product over any group. What remains is general
abelian-by-sofic soficity, which is open.

Proof: route `relation-cover-sofic-envelope-forces-trivial-kernel-proof`.
