---
rg: 2
id: toeplitz-folner-compressions-cannot-retain-jacobson-head
kind: claim
title: Truncated Toeplitz shifts pay exactly one Jacobson head in the one-sided-inverse relator
distinct_from:
  bounded-block-jacobson-microstates-also-collapse: that rules out bounded irreducible sectors abstractly; this rules out the natural unbounded finite-section sectors in every matrix dimension
  g2-conditioned-jacobson-sign-envelope-is-finite: that absorbs long-router sign words in a finite coefficient algebra; this audits the first obvious attempt to leave that algebra by truncated raw S and T
  qutrit-one-raw-letter-head-router-is-residually-finite: that constructs exact finite quotients for either orientation separately; this proves the standard two-orientation finite-section recombination cannot retain the head with small defect
---

Let `S_N,T_N` be the forward and backward truncated shifts on
`F_2^N`. With `P_0,P_(N-1)` the endpoint rank-one projections,

```text
T_N S_N=I-P_(N-1),              S_N T_N=I-P_0.          (TFC1)
```

Apply the elementary-matrix finite-section substitution

```text
x_ij(S) |-> X_ij(S_N),
x_ij(T) |-> X_ij(T_N)
```

inside `GL_(28N)(F_2)`, and then compose with an arbitrary
finite-dimensional unitary representation `rho_N` of that finite group.

For distinct fiber indices `i,j,k`, the defect of the Steinberg relation
which uses `TS=1` is exactly

```text
rho_N(X_ik(P_(N-1))).
```

The Jacobson head `x_ab(1-ST)` is sent to

```text
rho_N(X_ab(P_0)).
```

The two rank-one transvections are conjugate in
`GL_(28N)(F_2)`. Therefore, in every `rho_N),

```text
||rho_N(X_ik(P_(N-1)))-I||_2
 =||rho_N(X_ab(P_0))-I||_2.                             (TFC2)
```

Equation `(TFC2)` is independent of `N), the dimension of `rho_N`,
and its irreducible multiplicities. It also survives arbitrary direct sums
of finite-section sectors.

Consequently no truncated-shift/Folner compression followed by an ordinary
finite-group representation can produce Jacobson microstates with all
relator defects tending to zero and head defect bounded below. The boundary
of the one-sided-inverse relation is not diluted: representation-theoretic
conjugacy identifies it exactly with the marked head.

This is a construction firewall, not a global head modulus. It does not
cover non-functorial perturbations of the root unitaries or genuinely
projective finite-section maps with a controlled multiplier. Any successful
unbounded-dimensional microstate must use one of those mechanisms rather
than the literal Toeplitz truncations.

DERIVATION
boundary-transvection-is-conjugate-to-head-proof
