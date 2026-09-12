---
rg: 2
id: torsion-free-scalar-df-failure-gives-exotic-idempotents
kind: claim
title: A scalar one-sided inverse pair in a group algebra is a nontrivial idempotent, so on torsion-free hosts it refutes the idempotent conjecture
distinct_from:
  strict-idempotent-equivalence-breaks-direct-finiteness: that builds a direct-finiteness failure from a strict idempotent equivalence; this is the converse direction, reading a nontrivial idempotent off any scalar failure.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that reduces the idempotent conjecture over a field to one fixed torsion-free group; this shows every scalar linear Gottschalk counterexample on a torsion-free host already refutes that conjecture.
  stable-finiteness-failure-refutes-surjunctivity: that turns a matrix one-sided pair into a strict automaton; this constrains the scalar pairs that could feed it on torsion-free hosts.
artifacts:
  - research/artifacts/fournier-facio-torsion-free-host-constraints-2026-09-12.md
---

**ESTABLISHED.** Let `k` be a field, `G` a group, and `alpha, beta in k[G]` with
`beta alpha = 1 != alpha beta`. Then `e = alpha beta` is an idempotent with
`e != 0, 1`, and `e(1 - e) = 0` exhibits zero divisors.

If `G` is torsion-free, `e` refutes Kaplansky's idempotent conjecture for `k[G]`,
and hence, by `kaplansky-three-properties-fixed-fp-torsion-free-tester`, for the
fixed torsion-free tester host over `k`. So on the Fournier--Facio group, or on
any torsion-free host, a scalar linear Gottschalk counterexample through
`stable-finiteness-failure-refutes-surjunctivity` would first refute the idempotent
and zero-divisor conjectures there. By `invariant-output-injective-ca-need-torsion`,
its corner cannot be the averaging idempotent of a finite subgroup.

Matrix one-sided pairs at size `n >= 2` are not constrained by this. An embedding
of `k[G]` into a division ring would exclude them as well, but none is known for
the Fournier--Facio group.

Proof: `torsion-free-scalar-df-failure-gives-exotic-idempotents-proof`.
