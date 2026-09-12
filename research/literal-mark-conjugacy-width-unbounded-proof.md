---
rg: 2
id: literal-mark-conjugacy-width-unbounded-proof
kind: route
title: Apply the weak-soficity criterion to the sofic literal group, one relator width at a time
target: literal-mark-conjugacy-width-unbounded
requires: [literal-group-sofic, unsquared-defect-finite-model-invisible, glebsky-rivera-w-sofic-criterion]
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
  - GroupApproximation/Sofic/LiteralFiniteDimensionalObstruction.lean
---

**(a) The lift is in the profinite closure of `N` but not in `N`.**
`wt not-in N` is `literal_mark_ne_one`.  For the closure, let `q : F -> Q` be
any homomorphism to a finite group and replace `Q` by the finite image, so
`q` is onto and `q(N)` is normal in `Q`.  Then

```text
qbar : E = F/N -> Q/q(N),      f N |-> q(f) q(N)
```

is well defined, and `unsquared-defect-finite-model-invisible` — the Lean
`map_literal_mark_eq_one_of_finite`, applied to the left regular
representation of the target over `Q` — gives `qbar(w) = 1`, i.e.
`q(wt) in q(N)`.  Ranging over all finite `q` and using the finite-quotient
characterization of the profinite topology gives `wt in closure_prof(N)`.

**(b) No fixed width contains it.**  `literal-group-sofic` establishes that
`E` is sofic, hence weakly sofic (a symmetric group with normalized Hamming
metric is a finite group with a bi-invariant metric, so a sofic model is a
model in the sense of Glebsky--Rivera Definition 4.1).  So
`glebsky-rivera-w-sofic-criterion` applies in the **positive** direction:

```text
closure_prof( [a_1]^F ... [a_j]^F )  subseteq  N     for every finite
                                                    sequence a_i in N.
```

Every `a_i` drawn from `R ∪ R^(-1)` lies in `N`, and for fixed `m` the union
defining `P_m` is finite because `R` is a `Finset`.  Closure in a topological
space commutes with finite unions, so `closure_prof(P_m) subseteq N`.  Since
`wt not-in N`, we get `wt not-in closure_prof(P_m)`.

**(c) Unbounded width.**  Unwinding (b) through the finite-quotient
characterization: for each fixed `m` there is a finite quotient `q_m` with
`q_m(wt) not-in q_m(P_m)`.  Meanwhile (a) gives `q(wt) in q(N) = union_m q(P_m)`
for every finite `q`.  A uniform bound `m` would put `q(wt) in q(P_m)` for
that one `m` and every finite `q`, contradicting the existence of `q_m`.

**Where the topology enters.**  Only in (b), through "closure commutes with
finite unions".  That is what fails for the increasing union `N = union_m P_m`,
and (a) plus (b) is a concrete proof that it fails — the strictness is not
hypothetical.
