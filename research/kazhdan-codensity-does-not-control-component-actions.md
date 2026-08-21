---
rg: 2
id: kazhdan-codensity-does-not-control-component-actions
kind: claim
title: Kazhdan co-density and commensuration do not control the action on expander components
distinct_from:
  codense-kazhdan-coset-action-forces-permutation-outliers: that excludes exact and flexibly exactifiable finite orbit atlases; this constructs the far permutation-outlier architecture explicitly for another co-dense Kazhdan pair.
  projective-transfer-equals-rcc-for-perfect-pairs: that reduces projective transfer to relative-commutant collapse; this shows that perfectness, property T, finite-dimensional co-density, and commensuration still do not imply that collapse.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that gives a conditional falsifier for an arbitrary proper pair; this gives a pair for which the falsifier is unconditionally sofic/hyperlinear.
---

There exist finitely generated perfect groups `C<A` and an element
`h in A\C` such that:

1. `C` is infinite, residually finite, and has property `(T)`;
2. `C` is normal in `A` (hence `h` commensurates `C` with index one);
3. `C` is finite-dimensionally co-dense in the strongest sense

   ```text
   rho(C)=rho(A)                                        (KCA1)
   ```

   for every finite-dimensional unitary representation `rho` of `A`;
4. the coset action `A curvearrowright A/C` is sofic;
5. in product permutation microstates for `A`, the `C`-labeled graph is a
   disjoint union of uniform expanders while `h` acts nontrivially on the
   component set;
6. relative-commutant collapse fails in a Connes-embeddable tracial model.

Consequently, no Hecke-correspondence cluster theorem can follow from
property `(T)`, finite-dimensional co-density, and finite-index
commensuration alone.  The arithmetic pair

```text
SL_3(Z) < SL_3(Z[1/2])                                  (KCA2)
```

must use the specifically **non-normal, expanding** geometry of its
`SL_3(Q_2)/SL_3(Z_2)` Schlichting completion.

## Construction

Take

```text
C=SL_3(Z).                                              (KCA3)
```

Let `D` be a finitely generated infinite simple amenable group which is
LEF.  One concrete source is the derived topological full group of a
suitable minimal subshift: it is finitely generated and simple, amenability
is due to Juschenko--Monod, and the ambient topological full group is LEF by
Grigorchuk--Medynets.  Put

```text
A=C times D.                                            (KCA4)
```

Both factors are perfect (`D` is infinite nonabelian simple), so `A` is
perfect.  The subgroup `C=C times {1}` is normal and Kazhdan.

Every homomorphism from `D` to a finite group is trivial: its kernel is
normal, and an injective map from infinite `D` to a finite group is
impossible.  More strongly, every finite-dimensional unitary representation
of `D` is trivial.  A nontrivial one would be faithful by simplicity, but a
finitely generated linear group is residually finite (Malcev), contradicting
the absence of finite quotients of `D`.  Therefore every finite-dimensional
unitary representation of `A` kills `D`, proving `(KCA1)`.

On the other hand

```text
A/C ~= D,                                               (KCA5)
```

and the action of `A` on this quotient is the regular action of the sofic
group `D` (with `C` acting trivially).  It is a sofic action.

## The union-of-expanders microstate

Choose finite quotients

```text
q_n:C->Q_n                                              (KCA6)
```

separating larger and larger balls of `C`, and let `C` act regularly on
`X_n=Q_n`.  Property `(T)` gives a uniform expansion constant for these
Cayley graphs.  Choose a sofic/LEF approximation

```text
sigma_n:D->Sym(Y_n).                                    (KCA7)
```

On

```text
V_n=X_n times Y_n                                      (KCA8)
```

define the product approximation

```text
c.(x,y)=(q_n(c)x,y),
d.(x,y)=(x,sigma_n(d)y).                                (KCA9)
```

The `C`-labeled graph is exactly the disjoint union, indexed by `Y_n`, of
copies of the expander Cayley graph of `Q_n`.  For `h=(1,d_0)` with
`d_0!=1`, the permutation `sigma_n(d_0)` acts on the component index set.
It commutes **exactly** with every `C`-labeled edge, so it is an exact
automorphism of the union, although it need not preserve any individual
component.

The standard orbit charts extracted from `(KCA7)` approximate the regular
action `D curvearrowright D`, hence the coset action `(KCA5)`.  They live
entirely in the component index.  Internally, every component can be as
rigid an expander as desired without affecting this atlas.

This is the precise counterexample to the hoped-for cluster principle:

```text
rigid expander components
+ an almost/exact automorphism of their union
does not imply a finite action on the component labels. (KCA10)
```

The component action may instead be an arbitrary sofic approximation of a
group with no finite quotients.  Finite-dimensional co-density constrains
exact representations of `A`; it does not correct `(KCA7)` to an exact
finite action.

## Explicit relative-commutant failure

Choose noncommuting `u_0,d_0 in D`, and in the group factor `L(A)` put

```text
u=lambda((1,u_0)),
h=(1,d_0).                                              (KCA11)
```

Then

```text
u in L(C)' cap L(A),
[u,lambda(h)]!=1.                                       (KCA12)
```

The group `A` is sofic (indeed `C` is residually finite and `D` is
amenable), so `L(A)` is Connes embeddable.  Thus `(KCA12)` is a literal
matrix-ultraproduct failure of relative-commutant collapse despite all the
exact hypotheses above.

The generalized coset wreath product is also unconditional here:

```text
(direct_sum_(A/C) Z/2) semidirect A
 ~= C times ((direct_sum_D Z/2) semidirect D).          (KCA13)
```

It is sofic and hyperlinear.

## What Kun--Thom does and does not control

Kun--Thom's cluster theorem improves almost automorphisms of a **single**
expander and packages their Hamming clusters into a finite group.  In
`(KCA8)--(KCA9)`, `h` is instead an automorphism of a union of expanders and
acts in the unconstrained component direction.  Applying the theorem
inside each component sees only the identity internal automorphism; it does
not touch `sigma_n(d_0)`.

For `(KCA2)`, `h=diag(2,1,1/2)` does not normalize `C`.  It transports
finite-index subgroup graphs to transverse finite-index subgroup graphs,
so the relevant object is a Hecke correspondence, not an independent
permutation of identical components.  A viable arithmetic cluster theorem
must exploit this transversality.  A suitable quantitative target is:

> In a sofic approximation of `SL_3(Z[1/2])`, simultaneously decompose the
> `C`, `C cap hCh^(-1)`, and `hCh^(-1)` labeled graphs into their Kazhdan
> expander packets.  Prove that an almost `h`-correspondence which carries a
> positive-density `C`-fixed orbit label induces, after clustering, one
> finite permutation representation of the whole arithmetic pair.

Finite-dimensional co-density would then apply to that clustered
representation and the one-hot contradiction of
`codense-kazhdan-coset-action-forces-permutation-outliers` would finish.
The product example proves that the simultaneous **transverse subgroup**
clause cannot be omitted.

## Claim boundary

This note is a rigorous negative result about the available hypotheses.  It
does not construct an outlier for the arithmetic pair `(KCA2)` and does not
decide whether its building-vertex action is sofic.  It proves that the next
theorem must use the non-normal Bruhat--Tits Hecke geometry, rather than a
generic extension of property-`(T)` almost-automorphism rigidity.

## Literature

- Juschenko--Monod, *Cantor systems, piecewise translations and simple
  amenable groups*, Annals of Mathematics 178 (2013), 775--787, constructs
  finitely generated infinite simple amenable groups from minimal systems.
- Grigorchuk--Medynets, *On algebraic properties of topological full
  groups*, Sbornik Mathematics 205 (2014), 843--861, proves LEF for these
  topological full groups and records finite generation and simplicity of
  the derived group for minimal subshifts.
- Kun--Thom, *Inapproximability of actions and Kazhdan's property (T)*,
  arXiv:1901.03963 (updated 2026), proves the single-expander almost-
  automorphism cluster theorem whose union-of-components limitation is
  exposed above.
