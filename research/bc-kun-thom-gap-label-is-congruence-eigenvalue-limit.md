---
rg: 2
id: bc-kun-thom-gap-label-is-congruence-eigenvalue-limit
kind: claim
title: On a Kun--Thom actor the trace of a gapped spectral projection is the limit of congruence-quotient eigenvalue fractions
distinct_from:
  kun-thom-actor-algebraic-idempotents-pass-trace-test: that treats finite-spectrum elements, whose spectral projections are algebraic idempotents of M_n(C[G]) with trace forced into Z[1/P]; this treats a self-adjoint element of infinite spectrum, expresses its gapped spectral projection's trace as a congruence-quotient limit, and draws no integrality conclusion.
  kun-thom-actor-finite-subgroup-ring-equals-z-inverted-p: that identifies the finite-subgroup ring Lambda^G as Z[1/P]; this is the reduction of an infinite-spectrum gap label to a limit of finite eigenvalue fractions, the object whose membership in Z[1/P] is the open question.
artifacts:
  - research/artifacts/bc-kun-thom-trace-test-2026-09-12.md
---

**ESTABLISHED.** Let `G = EL_r(F_q[x_1^(+-1), ..., x_d^(+-1)]) semidirect SL_d(Z)`
with `r, d >= 3` be a Kun--Thom Theorem E actor, and let
`a = a* ∈ M_n(Q[G])`. Let `c ∈ R` lie in a gap of the spectrum of `lambda(a)`
in `M_n(C*_r G)`, i.e. an open interval around `c` is disjoint from
`spec(lambda(a))`. Then `chi = chi_((-inf,c))(lambda(a))` is a projection in
`M_n(C*_r G)`, and its normalized trace `taubar = tau / n`
(`taubar(1_n) = 1`, `tau(x) = sum_i x_ii(1)`) satisfies

```text
taubar(chi) = lim_(p' -> inf)  #{ eigenvalues of pi_(p')(a) below c } / ( n [G : N_(p')] ),
```

the limit over the congruence quotients `pi_(p') : G -> G/N_(p')` of
`kun-thom-actor-algebraic-idempotents-pass-trace-test`, taken over primes
`p' -> inf`. Equivalently, with the unnormalized trace,

```text
tau(chi) = lim_(p' -> inf)  #{ eigenvalues of pi_(p')(a) below c } / [G : N_(p')].
```

Here `pi_(p')(a)` is a Hermitian matrix of size `n [G : N_(p')]`, acting on
`C^n ⊗ l^2(G/N_(p'))` through the (left regular) representation of the finite
quotient.

**Why this is the surviving Baum--Connes test object.** By
`kun-thom-actor-algebraic-idempotents-pass-trace-test` every finite-spectrum
witness is disposed of, so a projection able to refute the trace test must be a
gapped spectral projection of an infinite-spectrum `a`. This claim pins the only
quantity in play, `tau(chi)`, to an explicit limit of rationals. It is a
reduction, **not** an integrality statement: whether the limit lies in
`Z/[1/P]` is exactly the open question recorded on
`baum-connes-counterexample-group-exists`, and this claim asserts nothing about
it. Since `tau(chi) = n · taubar(chi)`, the limit leaves `Z[1/P]` iff `tau(chi)`
does.

**Scope and correction.** The displayed identity uses the tracial STATE
`taubar = tau/n`. The Section 4 display of
`research/artifacts/bc-kun-thom-trace-test-2026-09-12.md` writes the
right-hand fraction `#{...}/(n[G:N])` against the unnormalized `tau(x) = sum_i
x_ii(1)`; under that convention the fraction equals `taubar(chi)`, not
`tau(chi)`, i.e. it carries one extra factor `1/n`. The two forms above are the
consistent statements.
