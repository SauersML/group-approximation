---
rg: 2
id: kervaire-laudenbach-nonsingular-conjecture
kind: claim
title: Nonsingular one-variable equations inject their coefficient group
root: true
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that is the theorem for hyperlinear coefficient groups, established here and the reason this graph cares about the conjecture at all; this is the universally quantified statement over all groups, which that theorem leaves open outside the hyperlinear class.
  kl-violating-equation-over-leavitt-unit-group: that asks for one explicit violating equation over one group, and establishing it would refute this; per the kernel's semantics a refutation is its own claim, so the two coexist and only one can end up established.
  weak-kervaire-transfers-only-at-unimodular-degree: that is the scope statement about what the weak conjecture does and does not deliver; this is the strong statement itself, and the point of that node is that it is not a route into this one.
artifacts:
  - research/artifacts/kervaire-laudenbach-audit-2026-08-17.md
---

For every group `G` and every `w in G * <t>` with `deg_t(w) = m != 0`, the
coefficient map

    G  -->  G_w  =  (G * <t>)/<<w>>

is injective.  Equivalently, every nonsingular one-variable equation
`w(t) = 1` has a solution in some group containing `G`.

This is the form used throughout this repository, after Nitsche--Thom
(see `kervaire-laudenbach-holds-for-hyperlinear` for their statement and the
citation correction).  It is **not** the weak conjecture — see
`weak-kervaire-transfers-only-at-unimodular-degree`.

Open.  Marimon--Pinsker, arXiv:2606.24741v2 (revised 10 August 2026), read
from source 2026-08-17: "it is a major open problem whether this phenomenon
might occur also for regular words", and "The one-variable case of this
question is the famous Kervaire-Laudenbach Conjecture, answered positively
for finite groups and for hyperlinear groups".

## Why it is a root of this graph

It is not this program's goal, and nothing here implies it.  It is a root
because this repository already runs a falsification lane through its
negation — `kl-violating-equation-over-leavitt-unit-group` feeding
`kl-violation-refutes-hyperlinearity-route` — and an external resolution
attempt was audited against that lane on 2026-08-17.  The attempt produced no
proof and no counterexample, but its reductions and obstructions are worth
keeping: they say what a counterexample must look like and they close five
attacks, two of which were live against the Leavitt lane.

Soficity, hyperlinearity and MF-ness are not evidence about this claim in
either direction.  The one implication that does run between them is the one
already recorded: hyperlinear coefficients satisfy it
(`kervaire-laudenbach-holds-for-hyperlinear`), so a counterexample group is
not hyperlinear.

## What a certificate must contain

*Proof.*  By `kl-via-simple-envelope-reduction` it is enough to prove it for
two-generator nonabelian simple coefficient groups, and by
`kl-simple-failure-leaves-only-the-cyclic-quotient` that case is exactly:
for every such `S`, every `m >= 1` and every `w` of exponent sum `m` in
`N_m = ker(S * <t> -> C_m)`, the ambient normal closure `<<w>>_{S*<t>}` is a
proper subgroup of `N_m`.  A certificate must therefore be a uniform source
of proper quotients, and by
`degree-kernel-abelianization-is-infinite-cyclic` it cannot be abelian.

*Disproof.*  A group `G`, a word `w in G * <t>` with `deg_t(w) != 0`, a
nontrivial `a in G`, and an explicit finite identity
`a = prod_j u_j w^{e_j} u_j^{-1}` in `G * <t>`.  The identity is the whole
certificate: everything else in the reduction package follows from it.

## Attempts

Six lanes were run against this repository's material on 2026-08-17 and all
six died at an identified step; `research/artifacts/kervaire-laudenbach-audit-2026-08-17.md`
carries the arguments.

1. **Magnus / near-identity fixed point.**  Solve the equation formally in a
   filtered ring and read the root off the fixed point.  *Dies* at
   `near-identity-embedding-forces-residual-nilpotence`: coefficients living
   in `1 + I` are residually nilpotent, and the reduction sends every
   counterexample into a simple, hence perfect, group.  Recorded as
   `kl-via-magnus-near-identity-fixed-point`.
2. **Hilbert-hotel block shift.**  Absorb the equation by rearranging
   infinitely many copies.  *Dies* at
   `block-monomial-root-forces-permutation-order`: the permutation part of
   `w(T)` is `sigma^m`, which is the identity at the only degree where the
   weak problem is hard.  Recorded as `kl-via-block-shift-hilbert-hotel`.
3. **Infinite-dimensional amplification**, and **existential closure**.
   *Both die* at `overgroup-room-does-not-supply-a-root`: each is a verbatim
   restatement of the conjecture, not a reduction of it.  Recorded as
   `kl-via-infinite-dimensional-amplification` and
   `kl-via-existentially-closed-overgroup`.
4. **Import a claimed proof of the weak conjecture.**  *Dies twice*: at
   `weak-kervaire-transfers-only-at-unimodular-degree`, because the weak
   conjecture's content is confined to `m = ±1` and the transfer is to
   unimodular injectivity only; and at
   `kawauchi-weak-kervaire-rests-on-unresolved-inputs`, because the claimed
   proof's own supporting manuscript states its dependence on the smooth
   unknotting and smooth 4D Poincaré conjectures.  Recorded as
   `kl-via-weak-conjecture-import`.
5. **Extend the hyperlinear proof by weaker approximation.**  Not refuted and
   *deferred*, as `window-controlled-finite-dimensional-root-theorem`: the
   Gerstenhaber--Rothaus degree argument needs a root whose whole evaluation
   path stays inside the window where the approximate representation is
   multiplicative and separating.  Point-strong approximation and nontracial
   state seminorms are not known to supply this; that is a gap in them, not a
   theorem against them, so nothing is invalidated.
6. **Binate-group and acyclic swindles.**  *Deferred*, and recorded here
   rather than as a node: they preserve homology, and the missing statement —
   that every finite set of coefficient inequations survives imposing
   `w = 1` — is the conjecture itself.

A seventh non-attempt worth writing down because it looks tempting from
inside this program: nonsoficity and non-MF-ness of a group are not evidence
that it violates this claim.  They supply no equation and no identity.
