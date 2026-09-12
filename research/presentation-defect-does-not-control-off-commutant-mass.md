---
rg: 2
id: presentation-defect-does-not-control-off-commutant-mass
kind: claim
title: Presentation defect cannot force a Toeplitz gauge into the carrier commutant
distinct_from:
  bounded-multiplicity-toeplitz-gauges-collapse-head: that assumes from the start that every gauge lies in the commutant; this proves that relator smallness alone cannot justify that assumption
  unbounded-commutant-coherence-is-the-original-gate: that classifies arbitrary gauges after exact carrier separation; this exhibits the obstruction to obtaining such a separation
  toeplitz-folner-compressions-cannot-retain-jacobson-head: that compares the two endpoint transvections inside one finite-group representation; this concerns arbitrary tuples measured relative to that representation
---

Let `F` be a finite group, `rho:F->U(H)` a unitary
representation, and

```text
E_comm(X)=|F|^(-1) sum_(g in F) rho(g)Xrho(g)^*
```

the trace-preserving conditional expectation onto `rho(F)'`. For every
matrix `X`,

```text
||X-E_comm(X)||_2^2
 = (1/(2|F|)) sum_(g in F)||[X,rho(g)]||_2^2.           (PDC1)
```

Thus an adjoint spectral gap can convert explicit commutator control into
distance from the commutant. Presentation defect, however, supplies no
such commutator control.

Indeed, let `P=<Sigma | R>` be any group presentation, let
`theta:Sigma->F` be any section, put `A_s=rho(theta(s))`, and for a
unitary tuple `U` define `Z_s=A_s^*U_s`. Take `rho=lambda_F` to be the
left regular representation and take the exact trivial tuple `U_s=I`.
Then `delta(U)=0`, while for every generator whose section value
`a=theta(s)` is noncentral,

```text
dist_2(Z_s,lambda_F(F)')^2 = 1-1/|a^F|.                (PDC2)
```

For a transvection in `F=GL_M(F_2)`,

```text
|a^F|=(2^M-1)(2^(M-1)-1),                              (PDC3)
```

so the off-commutant distance in `(PDC2)` tends to one. This is an exact
countermodel even though the regular carrier has the strongest available
finite-group averaging.

There is a second invariant obstruction. For every unitary `W`, the tuple

```text
U_s=W A_s W^*
```

has every relator defect and every marked-word norm exactly equal to those
of the carrier tuple `A`, but its relative gauges are the nonabelian
coboundaries

```text
Z_s=A_s^* W A_s W^*.
```

If a finite core `K<=F` is frozen, choosing `W in rho(K)'` preserves that
core exactly while still allowing `W notin rho(F)'`. Hence global frame
motion, and even motion invisible to a frozen proper core, can create
large off-commutant gauges without changing any word defect.

Consequently no dimension-free estimate

```text
max_s ||Z_s-E_comm(Z_s)||_2 <= f(delta(U)),  f(epsilon)->0,
```

can follow from the presentation relations alone. Any conditional-
expectation attack must add genuine relative data: a fixed global frame,
direct commutator tests, or an independently proved closeness of `U` to
the carrier. Expansion of `GL_M(F_2)` cannot manufacture the missing
hypothesis.

DERIVATION
regular-carrier-conditional-expectation-no-go-proof
