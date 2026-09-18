---
rg: 2
id: ce-standard-form-strategies-are-quantum-approximable
kind: claim
title: Commuting strategies in the standard form of a Connes-embeddable finite von Neumann algebra give quantum approximable correlations, for every vector state
distinct_from:
  llp-makes-hyperlinear-traces-amenable: that turns a hyperlinear trace on an LLP C-star algebra into an amenable one; this needs no LLP and no amenability, only trace-preserving lifting of finitely many projections and one bounded element, and it handles an arbitrary vector state with Bob in the commutant.
  standard-form-right-copy-does-not-freeze-zpc-controls: that shows that moving a readable algebra into the commutant does not produce a globally commuting frozen strategy; this is the positive statement that Alice in `M` and Bob in `M'` on `L^2(M)` already is a commuting strategy, and it is quantum approximable whenever `M` is Connes embeddable.
  state-support-corner-qwep-recovers-hyperlinearity: that recovers hyperlinearity from QWEP of a bidual support corner; this is a correlation-level consequence of Connes embeddability of the whole algebra.
---

**ESTABLISHED** by `ce-standard-form-strategies-are-quantum-approximable-proof`.
No novelty is claimed; this is the folklore microstate argument, written out
because the graph needs it with an arbitrary vector and no synchrony.

Let `(M,tau)` be a finite von Neumann algebra with faithful normal tracial
state, represented on `L^2(M,tau)` with trace vector `Omega` and modular
conjugation `J`, so `M'=JMJ`. Take finite question sets `X,Y`, answer sets
`A,B`, projection-valued measures `{P_(x,a)}_a` in `M` for each `x`, and
`{Q_(y,b)}_b` in `M'` for each `y`, and a unit vector `xi in L^2(M)`. Put

```text
p(a,b|x,y) = < P_(x,a) Q_(y,b) xi , xi >.                    (SFQ1)
```

If `M` is Connes embeddable, then `p in C_qa(X,Y,A,B)`, the closure of the
finite-dimensional tensor-product quantum correlations.

**Amplified form.** The same conclusion holds under three changes:
- the measurements are positive operator-valued;
- Alice's measurements lie in `M_F(M)` acting on `C^F (x) L^2(M)`, and Bob's lie in `M' (x) M_G` acting on `L^2(M) (x) C^G`, for finite `F,G`;
- `xi` is a unit vector of `C^F (x) L^2(M) (x) C^G`.

**Corollary.** If a countable group `Lambda` is hyperlinear, so that
`L(Lambda)` is Connes embeddable, then every correlation obtained from
projective measurements in `L(Lambda)` for Alice, in `L(Lambda)'` for Bob,
and any unit vector of `l^2(Lambda)` lies in `C_qa`. Equivalently, one finite
correlation `p notin C_qa` realized in this standard form over a finitely
presented `Lambda` exhibits a non-hyperlinear group.

Neither the vector state nor Bob's operators need any relation to the
canonical trace or to group elements. So the uniformity of canonical-trace
answer distributions behind `group-corner-exact-compilers-force-source-affine-safety`
is not an obstruction to such a witness.
