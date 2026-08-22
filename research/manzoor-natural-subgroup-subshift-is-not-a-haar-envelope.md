---
rg: 2
id: manzoor-natural-subgroup-subshift-is-not-a-haar-envelope
kind: claim
title: Manzoor's natural subgroup subshift is not a compact-abelian Haar envelope
distinct_from:
  manzoor-separation-does-not-specify-haar-cylinders: that proves the separated IRS is unnamed and its joint cylinder law is unavailable; this audits every compact or Bernoulli object that actually occurs in the primary construction and shows why none is already the required Haar action.
  manzoor-cdi-source-has-no-determined-koopman-gate: that isolates an unknown permutation-Koopman test for any hypothetical algebraic envelope; this gives three elementary source-specific failures of the natural subgroup-indicator and labeled-Schreier candidates before that test is reached.
  random-coset-lamp-correlations-realize-every-irs-character: that realizes membership as a fiberwise wreath correlation after the IRS has been supplied; this shows why the fibers present in Manzoor/AGV do not assemble into one fixed compact abelian Haar action.
---

The proof of Manzoor's non-co-hyperlinear IRS theorem contains no compact
abelian Haar action having the separated IRS as its stabilizer law or
equivariant factor.  The two compact/Bernoulli objects that actually occur in
the proof fail for concrete reasons.

First, the IRS is a probability measure `mu` on the closed conjugation
subshift

```text
Sub(F) subset {0,1}^F,       z_H(g)=1_(g in H).          (MSH1)
```

This is not an algebraic subshift for the ambient coordinatewise `C_2`
operation.  Every `z_H` has `z_H(e)=1`, so the set does not contain the zero
configuration; it is also not closed under coordinatewise addition.  Nor is
`mu` the restriction of ambient Bernoulli Haar measure.  For a nonabelian
free group choose infinitely many disjoint inverse pairs
`{g_n,g_n^(-1)}`.  Every subgroup indicator obeys

```text
z_H(g_n)=z_H(g_n^(-1))       for every n,               (MSH2)
```

whereas these independent equalities have Bernoulli-Haar probability
`product_n (1/2)=0`.  Thus `Sub(F)` is Haar-null in the only compact abelian
subshift explicitly surrounding it.

The conjugation action on `(MSH1)` also has the wrong stabilizers:

```text
Stab_F(H for conjugation)=N_F(H),                       (MSH3)
```

not `H`.  Hence its stabilizer IRS is the normalizer pushforward
`H |-> N_F(H)`, not Manzoor's `mu`, unless `H=N_F(H)` almost surely.  The
paper proves no such self-normalizing statement.  Using the canonical
subgroup space as the desired pmp realization therefore changes the trace
from `Pr(g in H)` to `Pr(g in N_F(H))`.

Second, the finite objects in Manzoor Section 3.2 are distributions on
**random pseudo-subgroups in finite word windows**.  They are solutions of
successive linear programs, not finite actions, finite groups, or uniform
measures on compact groups.  The proof chooses an optimizer at each window
and then an arbitrary weak-star cluster point.  It does not choose compatible
bonding maps between the optimizers, so this is not a profinite inverse
system.  Theorem 3.13 first obtains a separating game existentially, and the
proof of the main theorems then makes a further extreme-point choice of an
ergodic non-co-hyperlinear IRS.  No algebraic structure from a finite window
survives those choices.

Finally, the Abért--Glasner--Virág stabilizer realization cited in Manzoor
adds independent labels on each random Schreier set:

```text
first H~mu, then a Haar product label in [0,1]^(F/H).    (MSH4)
```

Conditioned on `H`, `(MSH4)` is a Bernoulli/Haar fiber and the fixed-`H`
lamp identity applies.  Globally the coordinate set `F/H` and its lamp group
vary with `H`, and the unresolved base measure is still `mu`.  Thus `(MSH4)`
is a relatively Bernoulli measurable bundle, not Haar measure on one fixed
compact abelian group acted on by automorphisms.  Turning it into such an
action is exactly the missing algebraic-envelope step, not a feature already
present in the source.

Consequently the actual Manzoor construction supplies no explicit Haar
factor to combine with the coset-lamp correlation.  This is stronger than a
mere absence of a formula: the obvious ambient Haar subshift is null and
nonalgebraic on the support, the obvious action records normalizers rather
than subgroup membership, and the finite approximants have no projective
action structure.

Primary sources: Manzoor,
[*There is an equivalence relation whose von Neumann algebra is not Connes
embeddable*](https://arxiv.org/html/2502.06697v2), Definitions 2.1, 2.3 and
3.7--3.11, Theorem 2.4, the proof of Theorem 3.6, Theorem 3.13 and the proof
of Theorems 1.1--1.2; Abért--Glasner--Virág,
[*Kesten's theorem for invariant random subgroups*](https://arxiv.org/abs/1201.3399),
Propositions 13--14.

