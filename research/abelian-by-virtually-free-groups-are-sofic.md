---
rg: 2
id: abelian-by-virtually-free-groups-are-sofic
kind: claim
title: Every abelian-by-virtually-free semidirect product is sofic
distinct_from:
  finite-type-linear-vfree-envelope-is-residually-finite: that proves the stronger residual-finiteness conclusion for finitely presented modules; this removes the finite-presentation and residual-finiteness hypotheses and proves soficity for every abelian module.
  nonresidual-linear-module-can-give-a-sofic-envelope: that is one explicit non-residually-finite example; this proves that soficity is automatic for the entire virtually-free-actor class.
  algebraic-envelope-principle: that compiles a genuinely non-Connes-embeddable algebraic crossed product; this rules out every such crossed product with a virtually free actor.
---

Let `A` be any countable abelian group, let `Lambda` be a finitely generated
virtually free group, and let

```text
Lambda -> Aut(A)                                           (AVS1)
```

be any action.  Then

```text
A rtimes Lambda                                            (AVS2)
```

is sofic.  No residual-finiteness, finite-presentation, or effectiveness
hypothesis on `A` is required.

Consequently, if `K=A-hat` and `Lambda` acts on `K` by the dual continuous
automorphisms, then

```text
L^infinity(K,Haar) rtimes Lambda ~= L(A rtimes Lambda)      (AVS3)
```

is Connes embeddable.  It cannot contain a trace-preserving copy of a
non-Connes-embeddable tracial von Neumann algebra, even by a non-Cartan or
non-base-equivariant embedding.

## Proof

### Free actors

First let `Lambda=F_r=<t_1,...,t_r>` and write `alpha_i` for the automorphism
of `A` induced by `t_i`.  Starting with `G_0=A`, define successively

```text
G_i = < G_(i-1), t_i |
        t_i a t_i^(-1) = alpha_i(a) for every a in A >.     (AVS4)
```

This is an HNN extension of `G_(i-1)` whose two associated subgroups are
copies of `A`.  They are amenable.  A sofic group remains sofic under an HNN
extension over an amenable associated subgroup.  This is Proposition 3.2 of
Ciobanu--Holt--Rees, *Sofic groups: graph products and graphs of groups*,
Pacific J. Math. 271 (2014), based on the amenable-amalgamation theorem of
Elek--Szabo, *Sofic representations of amenable groups*, arXiv:1010.3424.
Since `G_0=A` is amenable and hence sofic, induction gives that every `G_i`
is sofic.

Britton normal form identifies the final group with the desired semidirect
product:

```text
G_r ~= A rtimes F_r.                                      (AVS5)
```

There are no extra relations among the stable letters because `F_r` is free.

### Virtually free actors

Now let `Lambda` be finitely generated virtually free.  It has a normal
free subgroup `F` of finite index: start with a finite-index free subgroup,
take its finite-index normal core, and use Nielsen--Schreier.  The subgroup

```text
A rtimes F normal A rtimes Lambda                          (AVS6)
```

is sofic by the free case, and the quotient `Lambda/F` is finite, hence
amenable.  Sofic groups are closed under extensions with sofic kernel and
amenable quotient (Elek--Szabo, *On sofic groups*, arXiv:math/0305352).
Therefore `(AVS2)` is sofic.

Finally, Pontryagin Fourier transform gives `(AVS3)`, and group von Neumann
algebras of sofic groups are Connes embeddable.

## Consequence for the algebraic-envelope route

Manzoor's native acting group is virtually free.  Therefore **no** compact
abelian Haar action of that same group can supply the desired non-CE ambient
crossed product, regardless of whether its dual module is finite type,
recursively presented, or non-residually finite.  A non-Cartan placement does
not evade the obstruction because the whole ambient algebra `(AVS3)` is CE.

Thus every surviving algebraic-envelope construction must change the acting
group away from the native virtually-free actor.  Infinite module relations
alone are not a live repair.
