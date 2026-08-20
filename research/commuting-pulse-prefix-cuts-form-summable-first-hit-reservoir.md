---
rg: 2
id: commuting-pulse-prefix-cuts-form-summable-first-hit-reservoir
kind: claim
title: Prefix cuts of the pulse words themselves defeat every persistent tail character
distinct_from:
  free-root-top-boundary-reservoir-is-summable: that partitions characters by their first nonzero monomial coefficient; this partitions by first negative pulse and needs no coefficient-valuation claim.
  triangular-e5-pulses-admit-persistent-tail-character: that shows one character may be negative on every pulse; here that character exits at its first negative pulse and is absent from all later prefix carriers.
  hard-sign-transport-captures-exit-mass: that puts mass in one negative hard-sign space; this adds the prefix-preservation term needed to put it in a summable first-hit space.
---

Let `B_0,B_1,...` be commuting self-adjoint involutions, let `C_0` be a
projection commuting with them, and define

```text
C_n=C_0 product_(k<n)(I+B_k)/2,
X_n=C_n(I-B_n)/2.                                     (PCF1)
```

Then

```text
C_n=C_(n+1)+X_n,      X_n X_m=0 for n!=m,
sum_(n<N)tau(X_n)<=tau(C_0).                          (PCF2)
```

Thus first-hit summability may use the pulse words directly; their polynomial
coefficient supports may overlap arbitrarily.

More quantitatively, let `A_n` be an involution, `P_n` a projection with
`A_nP_n=-P_n`, and `V_n` a unitary.  Put `R_n^-=(I-B_n)/2`.  Since `C_n`
commutes with `R_n^-`,

```text
tau(P_n)-tau(X_n V_n P_n V_n^*)
 <= (1/4)||B_nV_n-V_nA_n||_2^2
    +||(I-C_n)V_nP_n||_2^2.                           (PCF3)
```

The first term is the hard-sign covariance defect.  The second is the exact
remaining prefix-leakage obligation.  In particular, persistent pulse-tail
characters do not obstruct the method once transported packet exits preserve
`C_n`.

For every fixed depth, approximate commuting involutions can first be
exactified as one finite elementary abelian packet.  Transport of the atom
`C_n` then has only linear-in-`n` sign-word loss, as in `(SAT2)`; no
exponential sum over its `2^n` characters occurs.
