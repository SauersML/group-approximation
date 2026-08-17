---
rg: 2
id: glebsky-rivera-w-sofic-criterion
kind: claim
title: Weak soficity of a free quotient is exactly profinite closure of bounded conjugacy products
distinct_from:
  glebsky-weak-soficity-is-metric-free: that records what Glebsky's 2023 permanence proof supplies and withholds (no metric at all); this is the 2008 Glebsky--Rivera characterization of weak soficity itself, in profinite-topology terms, and it is where the metric is manufactured rather than imported
  glebsky-manufactured-invariant-length: that is the 2017 construction of the capped conjugation-invariant word length, read as an input to the permanence theorem; this is the 2008 equivalence whose reverse direction that length proves, stated as a property of the normal subgroup rather than of a length
  glebsky-fin-case-instantiation: that pins the error and separated sets of the 2017 construction in the Fin case; this is the earlier and coarser statement, which never mentions an approximation and quantifies only over conjugacy products in the free group
  weakly-sofic-not-sofic: that is the separation of weak soficity from soficity, obtained from a permanence theorem plus Kun--Thom; this is a criterion internal to weak soficity that says nothing about soficity
  sofic-stable-implies-residually-finite: that imports a different Glebsky--Rivera paper (Almost solutions of equations in permutations, 2009) about stability of sofic groups; this is the 2008 paper on profinite topology, and the two share no statement
  sign-free-quotient-sofic: that establishes soficity of one specific group, the sign-free commuting-lamp quotient, by a permanence argument; this is a general equivalence about every finitely presented quotient of a free group, in a different approximation class, and proves no group sofic
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

Let `F` be a finitely generated free group and `N normal F`.  Then

```text
F/N is weakly sofic
  <=>  for every finite sequence g_1,...,g_k in N,
       closure_prof( [g_1]^F [g_2]^F ... [g_k]^F )  subseteq  N
```

where `[g]^F` is the `F`-conjugacy class of `g`, the product is the setwise
product of conjugacy classes taking **exactly one** conjugate of each listed
element in the listed order, and `closure_prof` is closure in the profinite
topology on `F` — equivalently, `x` lies in the closure iff
`q(x) in q([g_1]^F...[g_k]^F)` for every homomorphism `q` from `F` to a
finite group.

This is Glebsky--Rivera, *Sofic groups and profinite topology on free
groups*, J. Algebra **320** (2008), no. 9, 3512--3518, Theorem 4.3.  Weak
soficity here is their Definition 4.1: a fixed `alpha>0` such that every
finite `Phi` and every `eps>0` admit a `(Phi,eps,alpha)`-homomorphism into
**some** finite group with **some** bi-invariant metric, the metric not
required to be normalized.

## Why this node exists in this graph

The graph already carried weak soficity as a *permanence* story — Glebsky's
2023 extension theorem, the length his 2017 paper manufactures, and the
`weakly-sofic-not-sofic` separation it yields.  What it did not carry is the
criterion that decides the class outright, and that criterion is what makes
`non-weakly-sofic-group` a finite-word question rather than an
approximation-theoretic one.  Three consequences follow immediately and are
recorded as their own nodes:

- `non-weakly-sofic-finitely-presented-reduction` — any non-weakly-sofic
  group forces a finitely presented one (their Corollary 4.4);
- `non-weakly-sofic-word-certificate` — the exact finite certificate a
  construction must exhibit (their Conjecture 2.1, equivalent to existence by
  their Corollary 4.6);
- `literal-mark-conjugacy-width-unbounded` — the criterion applied *against*
  this repository's own non-MF witness, which is sofic, hence weakly sofic,
  hence supplies no escape.

## The direction that manufactures a metric

The hard direction is the reverse one, and it is where the "arbitrary
bi-invariant metric" freedom is spent.  Given the closure condition, one
fixes a word radius `R` and tolerance `eta`, sets

```text
X := N ∩ B_R     (finite, symmetric)
Y := B_R \ N     (finite)
```

takes `n > 1/eta`, and uses the closure condition to find, by a finite
diagonal product of finite quotients, a single `q : F -> H` with

```text
q(y) not-in [q(x_1)]^H ... [q(x_m)]^H     for all y in Y, m <= n, x_i in X.
```

Then with `C := union_(x in X) [q(x)]^H`, the capped rescaled conjugate-word
length

```text
l(h) := min{ L_C(h)/n , 1 },     L_C = word length in the conjugacy-closed
                                 generating set C, infinity if not generated
```

is a bi-invariant length with `l(q(x)) <= 1/n < eta` on the relators and
`l(q(y)) = 1` on everything of length `<= R` outside `N`.  That is exactly
the object already recorded on `glebsky-manufactured-invariant-length` from
the 2017 paper; the 2008 paper builds the same length from a *conjugacy
class graph* and rescales by `eps` instead of capping at 1.

**So the criterion and the length are the same fact seen from two sides**,
and the graph's existing Hilbert-embeddability programme is testing precisely
the metric this criterion produces.

## The forward direction is where "bounded" comes from

If `F/N` is weakly sofic with separation `alpha`, and `g_1,...,g_k in N`,
then for `x not-in N` one takes a model of accuracy small enough that
`d(q(g_i),1) < alpha/(2k)` while `d(q(x),1) > alpha`.  A product of exactly
`k` conjugates has length at most `sum_i d(q(g_i),1) < alpha/2` by
conjugation-invariance and subadditivity, so it cannot equal `q(x)`.

The count `k` is what makes this work: the triangle inequality is applied
`k` times against a separation that does not shrink.  An unbounded number of
conjugates would defeat it, which is why the criterion is about **fixed**
products of conjugacy classes and not about the normal closure.  That
distinction is the entire content of `literal-mark-conjugacy-width-unbounded`
and of the corpus's own `IsBoundedConjProduct` API.
