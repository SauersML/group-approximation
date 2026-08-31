---
rg: 2
id: mikhailova-left-right-frontier-proof
kind: route
title: Separate exact subgroup models from the surviving faithful external-color code
target: mikhailova-left-right-action-current-frontier
requires:
  - commuting-sofic-actions-need-not-combine
  - mihailova-left-right-local-models-do-not-see-q
  - mikhailova-left-right-soficity-is-one-color-code
  - mikhailova-color-code-schreier-irs-firewall
  - mikhailova-color-code-must-escape-finite-palettes
  - mikhailova-left-right-lef-iff-quotient-rf
  - mikhailova-left-right-action-sofic-for-lea-quotients
  - commutator-defect-survives-standard-amplification
---

## Presentation independence

Let `q_i:F_i->H` be two finite free presentations.  Choose lifts in
`F_1` of a free basis of `F_2`; they define a homomorphism
`s:F_2->F_1` with `q_1 s=q_2`.  The action belonging to `q_2` is
the pullback of the action belonging to `q_1` along `s x s`.
Restriction to `im(s x s)` and pullback through
`F_2 x F_2->im(s x s)` preserve soficity by GKP Proposition 2.15.
Reversing the roles of the presentations proves equivalence.

## Exact subgroup models stop at residual finiteness

For a transitive action `G` on `G/M`, residual finiteness as a
`G`-set is equivalent to separability of `M` in `G`.

If `H` is residually finite and `(u,v) notin M_H`, choose a finite
quotient `c:H->C` with `c(q(u)) != c(q(v))`.  Then
`(c q) x (c q)` sends `M_H` into `Delta C` but does not send
`(u,v)` there, so `M_H` is separable.

Conversely assume `M_H` is separable.  If `q(w) != 1`, then
`(w,1) notin M_H`, so some finite quotient
`theta:F_m x F_m->K` satisfies

```text
theta(w,1) notin theta(M_H).                           (MFP1)
```

Put `A=theta(F_m x {1})` and `D=theta(N x {1})`.  The subgroup
`D` is normal in `A`, and `(MFP1)` implies
`theta(w,1) notin D`.  Thus `F_m->A/D` kills `N` but not `w`,
and factors through a finite quotient of `H` separating `q(w)`.

For finitely presented `H`, [[mikhailova-left-right-lef-iff-quotient-rf]]
strengthens this to

```text
left-right action is LEF
 iff M_H is separable
 iff H is residually finite.                           (MFP2)
```

The finite generation of `M_H` makes rooted Chabauty convergence force
eventual finite-index overgroups of `M_H`, so pointed finite Schreier
models do not provide a weaker route.

## Why the published counterexample does not transfer

Kun--Thom plus GKP gives a nonsofic action

```text
G x G acts on (G x G)/Delta Gamma
```

with `Gamma<G` infranormal and Kazhdan.  It proves that two commuting
sofic coordinate actions need not combine.  It supplies no permanence of
nonsoficity under precomposition by an epimorphism.  GKP Proposition 2.15
gives the opposite one-way statement: a sofic quotient action pulls back to
a sofic action.  The reverse implication is false as a general proof
principle: `F_m` acting on `F_m/N` is sofic for every `N`, although
the quotient group `F_m/N` can be nonsofic.  Finite normal generation of
`N` does not change this.

## Exact one-color and commuting-centralizer criterion

By GKP Proposition 2.9 and
[[mikhailova-left-right-soficity-is-one-color-code]], the action is sofic
exactly when there are a homomorphism
`Phi:F_m x F_m->S_U` and one point `xi in X_U` such that

```text
d_U(Phi(g)xi,xi)=0     for g in M_H,
d_U(Phi(g)xi,xi)=1     for g notin M_H.                (MFP3)
```

Put `a(w)=Phi(w,1)` and `b(w)=Phi(1,w)`.  The ranges commute, and the
factorization

```text
(u,v)=(uv^(-1),1)(v,v)
```

turns `(MFP3)` into the exact conditions

```text
a(N)xi=xi,
a(w)b(w)xi=xi                     for w in F_m,
d_U(a(w)xi,xi)=1                  for w notin N.        (MFP4)
```

Because `F_m x F_m` is residually finite, one can take the product of
any witness with asymptotically free regular finite quotients and pull the
color back from the first coordinate.  This preserves every coefficient in
`(MFP3)` and makes `Phi` injective.  Actor faithfulness is therefore
not the obstruction.

If `H=<X|R>`, invariance in `(MFP4)` reduces to the finitely many
conditions

```text
a(r)xi=xi       (r in R),          a(x)b(x)xi=xi       (x in X).   (MFP5)
```

Diagonal invariance and `[a(F_m),b(F_m)]=1` propagate each relator
through its normal closure.  Only separation of every word outside `N`
remains global.

## Positive frontier and its coordinate boundary

If `H` is LEA, finite multiplication packets embed in an amenable group
`K`.  The images of the free generators extend to `F_m->K`, the
required finite orbit packet embeds in the left-right action
`K x K` on `K`, and GKP soficity of amenable-group actions pulls back.
This proves [[mikhailova-left-right-action-sofic-for-lea-quotients]].
Residually amenable groups are LEA by taking a finite product of amenable
quotients separating the requested finite packet.

This construction cannot be globalized by maps `z_n:A_n->H` satisfying
`z_n(L_s a)=s z_n(a)` off a vanishing exceptional set.  The pushforwards
of uniform measure would be asymptotically invariant probability measures
on `H`; Reiter's criterion would make `H` amenable.  The property-`(T)`
host therefore requires a non-coordinate code.

## Three further firewalls

1. **Schreier and IRS.**  Exact pointed Schreier convergence is already
   `(MFP2)`.  Uniform roots produce IRSs, whereas `delta_(M_H)` is an
   IRS only if `M_H` is normal, equivalently only if `H` is abelian.
   After faithful amplification, ordinary random point stabilizers instead
   tend to `{1}`.  Finite color-equality sets need not be subgroups.
   See [[mikhailova-color-code-schreier-irs-firewall]].
2. **Palette escape.**  For `m` distinct quotient elements and any set
   `C` of `K` colors, pairwise translated-color agreement at most
   `epsilon_n` gives
   `mu_n(C)<=K/m+(m-1)epsilon_n/2`.  Since
   `epsilon_n->0` and `m` is arbitrary, every fixed-size palette has
   mass tending to zero.  A bounded or tight finite observable cannot
   carry the code.  See
   [[mikhailova-color-code-must-escape-finite-palettes]].
3. **Amplification.**  If two finite permutations have commutator defect
   `delta`, their coordinatewise `k`-fold powers have defect
   `1-(1-delta)^k>=delta`, and disjoint unions preserve `delta`.
   Thus standard amplification cannot manufacture the cross-commutation
   needed by `F_m x F_m`.  See
   [[commutator-defect-survives-standard-amplification]].

## Attempts closed and the surviving object

- **Finite equivariant quotients, LEF, and pointed Schreier models:** exactly
  residual finiteness of `H`.
- **Arbitrary finite metric patches:** universal for the residually finite
  actor and quotient-blind.
- **LEA/Foelner packets or one global `H`-coordinate:** stop at amenability
  or LEA.
- **Separate left and right charts:** not a valid permanence principle, and
  ordinary amplification does not repair their commutators.
- **Descent from the nonsofic `H x H` action:** no reverse pullback theorem
  exists.
- **Uniform-root/co-sofic IRS methods:** target a non-IRS subgroup in the
  nonabelian case and ignore the external color stabilizer.
- **Bounded colors or a finite observable:** contradicted by palette escape.
- **Levelwise correction:** unavailable because `F_m x F_m` is not even
  very flexibly permutation stable.

None of these failures proves soficity or nonsoficity.  The fixed
nonsofic property-`(T)` host remains open, with exact missing object the
faithful commuting-centralizer external-color code `(MFP4)--(MFP5)`.

## References

Gao--Kunnawalkam Elayavalli--Patchell, *Research in the Mathematical
Sciences* 12 (2025), Propositions 2.9 and 2.15 and Theorem 2.19; Ioana,
arXiv:1909.00282; Kun--Thom, arXiv:2608.06222 via the existing verified
node.
