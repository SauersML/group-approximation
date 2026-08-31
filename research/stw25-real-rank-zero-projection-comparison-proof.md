---
rg: 2
id: stw25-real-rank-zero-projection-comparison-proof
kind: route
title: Exhaust positive elements by projections and collapse K0 states to the unique trace
target: stw25-real-rank-zero-k0-perforation-is-exact-obstruction
requires: []
artifacts:
  - research/artifacts/stw25-real-rank-zero-k0-audit-2026-08-30.md
---

Let `tau` be the unique tracial state of `A`, extended in the usual way to
matrices and to `A tensor K`.

## From weak unperforation to comparison of projections

Every normalized state on the ordered group

```text
(K_0(A),K_0(A)_+,[1_A])
```

is induced by a normalized quasitrace on `A` by the
Blackadar--Rordam state-extension theorem.  Nuclearity implies exactness, so
Haagerup's theorem makes that quasitrace a trace.  Uniqueness of `tau`
therefore makes the ordered `K_0`-group uniquely stated.

Under the present simple, stably finite, real-rank-zero, stable-rank-one, and
weak-unperforation hypotheses, Dadarlat's Proposition 2.8 gives that the
strict order on `K_0` is detected by its states:

```text
K_0(A)_+={0} union
 {x: s(x)>0 for every normalized K_0-state s}.                  (1)
```

This is the standard fundamental-comparison consequence of weak
unperforation.  Thus, if `p,q in A tensor K` are projections and
`tau(p)<tau(q)`, then `(1)` gives

```text
[q]-[p] in K_0(A)_+ minus {0}.                                  (2)
```

Stable rank one gives cancellation of projections.  Consequently `(2)`
upgrades from a Grothendieck-group statement to Murray--von Neumann
subequivalence:

```text
p is Murray--von Neumann subequivalent to q.                    (3)
```

## Real rank zero promotes projection comparison to strict comparison

Take `a,b in (A tensor K)_+` with

```text
d_tau(a)<d_tau(b).                                               (4)
```

Real rank zero passes to stabilization and hereditary subalgebras.  Since
these hereditary subalgebras are sigma-unital, choose increasing approximate
units of projections

```text
(p_n) in Her(a),             (q_m) in Her(b).
```

Normal monotone convergence in the tracial GNS representation gives

```text
sup_n tau(p_n)=d_tau(a),     sup_m tau(q_m)=d_tau(b).             (5)
```

Fix `n`.  Equations `(4)`--`(5)` provide an `m` with
`tau(p_n)<tau(q_m)`.  Projection comparison `(3)` gives

```text
p_n is Cuntz subequivalent to q_m is Cuntz subequivalent to b.
```

The Cuntz classes `[p_n]` increase to `[a]`; hence `[a]<=[b]`.  Thus `A`
has strict comparison of positive elements.

For a nuclear simple unique-trace algebra, uniform property Gamma is
automatic from the finite-dimensional compact extreme-boundary theorem
(equivalently, from the unique hyperfinite GNS fibre together with Sato's
central-sequence surjection and trace-kernel sigma-ideal lifting).  The
Castillejos--Evington--Tikuisis--White characterization

```text
strict comparison + uniform Gamma  iff  Z-stability
```

now proves the reverse implication in `(RR0-K)`.

For the forward implication, the Gong--Jiang--Su ordered-`K_0` theorem says
directly that a simple unital Z-stable algebra has weakly unperforated
`K_0`.  Equivalently in the present stable-rank-one setting, one may restrict
Rordam's almost-unperforation theorem to the cancellative projection
semigroup.  This completes both directions.
