---
rg: 2
id: mikhailova-left-right-action-current-frontier
kind: claim
title: The Mikhailova left-right action is an intrinsic free-cover problem not decided by the commuting-action counterexample
distinct_from:
  mikhailova-central-rope-is-a-left-right-action-wreath: that identifies the rope with the free wreath over this action; this determines what is known and what remains open about the action itself.
  commuting-sofic-actions-need-not-combine: that gives a nonsofic combined action with diagonal stabilizer inside a Kazhdan pair; it does not decide the pullback of the full diagonal action through a free presentation.
  mihailova-left-right-local-models-do-not-see-q: that proves arbitrary finite metric patches exist; this records the exact finite-Schreier boundary and the surviving positive-density Hamming condition.
  mikhailova-left-right-soficity-is-one-color-code: that gives the exact ultraproduct criterion; this root records its consequences, positive frontier, and surviving open case.
---

Let `q:F_m->H` be an epimorphism, `N=ker(q)`, and

```text
M_H={(u,v) in F_m x F_m:q(u)=q(v)}.
```

Under `(F_m x F_m)/M_H isomorphic to H`, the coset action is

```text
(u,v).h=q(u)h q(v)^(-1).                              (MLF1)
```

The following boundary is established.

1. Soficity of `(MLF1)` is independent of the chosen finite free
   presentation of `H`.
2. The action is residually finite, and equivalently `M_H` is separable,
   if and only if `H` is residually finite.  For finitely presented
   `H`, the stronger LEF action property is equivalent to the same
   condition.  Thus the compiler host is not LEF and admits no pointed
   finite Schreier approximation.
3. If `H` is LEA (initially subamenable), then `(MLF1)` is GKP-sofic.
   This includes amenable, LEF, and residually amenable quotients.  It
   cannot reach the fixed nonsofic host, since every LEA group is sofic.
4. Alekseev--Thom local metric models exist for every `H` and do not
   decide the action.  A stronger construction with one approximately
   equivariant global `H`-valued root coordinate would force `H` to be
   amenable, so it is impossible for the property-`(T)` host.
5. The Kun--Thom counterexample to combining commuting sofic actions does
   not imply that `(MLF1)` is nonsofic.  Its stabilizer is
   `Delta Gamma<G x G` for an infranormal Kazhdan subgroup; here the
   stabilizer is the full inverse image `(q x q)^(-1)(Delta H)`.
   Nonsoficity does not descend from the quotient actor `H x H` to its
   free cover, and each coordinate restriction remains a sofic free-group
   action.
6. Ioana's failure of very flexible permutation stability for
   `F_m x F_m` blocks levelwise exactification.  Standard amplification
   does not repair the problem either: a commutator defect `delta` becomes
   `1-(1-delta)^k>=delta` on a `k`-fold coordinate power and remains
   `delta` on a disjoint union.
7. Pointed Schreier limits and IRS limits see the wrong data.  Pointed
   convergence is the separability condition above.  A uniform root would
   target `delta_(M_H)`, but this is an IRS only when `H` is abelian.
   Every hypothetical GKP witness can instead be amplified so the actor
   embedding is faithful and its ordinary random stabilizers tend to
   `{1}`; `M_H` survives only as an external color stabilizer.
8. For infinite `H`, that external color is necessarily diffuse.  For
   every fixed `K`, the maximum mass carried by any `K` colors tends
   to zero.  Hence no bounded alphabet, tight finite palette, or finite
   observable can be collapsed to a quotient action.

## Exact remaining object

By the one-color reduction, `(MLF1)` is sofic exactly when there are
commuting homomorphisms

```text
a,b:F_m->S_U
```

and a color point `xi in X_U` such that

```text
a(n)xi=xi                         for n in N,
a(w)b(w)xi=xi                     for w in F_m,
d_U(a(w)xi,xi)=1                  for w notin N.        (MLF2)
```

The combined homomorphism `Phi(u,v)=a(u)b(v)` may be required to be
injective.  If `H=<X|R>` is finitely presented, all invariance in
`(MLF2)` reduces to the finite tests

```text
a(r)xi=xi       (r in R),          a(x)b(x)xi=xi       (x in X),   (MLF3)
```

while maximal displacement for every `w notin N` remains global.

Thus for the fixed nonsofic property-`(T)` Mikhailova quotient, soficity
of `(MLF1)` remains **OPEN**.  The missing object is precisely the
faithful commuting-centralizer external-color code `(MLF2)--(MLF3)`.
It is not supplied by separate coordinate charts, finite quotients, LEF or
LEA models, local metric patches, bounded palettes, Schreier/IRS limits,
global quotient coordinates, stability, or standard amplification.

Relevant exact reductions:
[[mikhailova-left-right-soficity-is-one-color-code]]
[[mikhailova-color-code-schreier-irs-firewall]]
[[mikhailova-color-code-must-escape-finite-palettes]]
[[mikhailova-left-right-lef-iff-quotient-rf]]
[[mikhailova-left-right-action-sofic-for-lea-quotients]]
[[commutator-defect-survives-standard-amplification]]

DERIVATION
[[mikhailova-left-right-frontier-proof]]
